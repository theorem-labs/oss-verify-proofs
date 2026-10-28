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
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnParSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParKit.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSrcSMemmove_u PnSrcSReadP_u Bs0_code_r368b0_368b4_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PGSRD.
Import PMS.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

(* [comment removed for export] *)
Lemma rd_cpy LB cr (fx : FPState) R M model K (dst src n ra : Z) :
  hi_heap HI LB cr M (m_vmmaps model) -> m_halted model = None -> m_vm_lazy model = [] -> 0x7fff80000000 <= hl_sptop L ->
  getr R (PMK.reg 10) = Z_to_bv 64 dst -> getr R (PMK.reg 11) = Z_to_bv 64 src -> getr R (PMK.reg 12) = Z_to_bv 64 n ->
  getr R (PMK.reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra ->
  1 <= n -> 0 <= dst -> dst + n < 2 ^ 63 -> 0 <= src -> src + n < 2 ^ 63 -> (dst + n <= src \/ src + n <= dst) ->
  L5.defined M dst n -> L5.defined M src n -> (forall a, dst <= a < dst + n -> PMK.cwr L LB a) ->
  (forall R3 M3, mem_grows M M3 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + n) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      L5.defined M3 dst n -> (forall i, In i L5K.CS -> getr R3 (PMK.reg i) = getr R (PMK.reg i)) ->
      hi_heap HI LB cr M3 (m_vmmaps model) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R3 ra M3 model) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xab480 M model) K.
Proof.
  intros HH Mh Ml TOP H10 H11 H12 H1 RA Hn Hd Hdn Hs Hsn AP DD DS CW KONT.
  destruct (PMCPS.memcpy_run fx R M dst src n ra H10 H11 H12 H1 RA Hn Hd Hdn Hs Hsn AP
              ltac:(apply (L5C.writable_of_defined RSEGS); [exact DD| lia| lia]) DS) as (R3 & M3 & MS & MG & FRZ & D3 & KS & _).
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx R 0xab480 R3 ra M3 (fun a => dst <= a < dst + n) K HH Mh Ml TOP MS MG FRZ CW
           (fun a => PMK.rng_dec a dst (dst + n))).
  intros HH3. apply KONT; assumption.
Qed.

Lemma nodup3 (a b c : Z * Z) l : NoDup (map fst (a :: b :: c :: l)) -> fst a <> fst b /\ fst a <> fst c /\ fst b <> fst c.
Proof.
  intros ND. cbn [map] in ND. inversion ND as [|x l1 NI1 ND1]. subst. inversion ND1 as [|y l2 NI2 ND2]. subst.
  split; [|split]; intros E.
  - apply NI1. rewrite E. constructor.
  - apply NI1. rewrite E. constructor. constructor.
  - apply NI2. rewrite E. constructor.
Qed.

Lemma apart_pt (x n y m : Z) : 1 <= n -> 1 <= m -> (forall a, x <= a < x + n -> ~ (y <= a < y + m)) -> x + n <= y \/ y + m <= x.
Proof.
  intros Hn Hm H. destruct (Z_lt_le_dec x y) as [L1|L1].
  - left. destruct (Z_le_gt_dec (x + n) y) as [X|X]; [exact X|]. exfalso. apply (H y); lia.
  - right. destruct (Z_le_gt_dec (y + m) x) as [X|X]; [exact X|]. exfalso. apply (H x); lia.
Qed.
Lemma defined_app (M : word -> option byte) a n1 n2 : 0 <= n1 -> L5.defined M a n1 -> L5.defined M (a + n1) n2 -> L5.defined M a (n1 + n2).
Proof.
  intros H0 D1 D2 i Hi. destruct (Z_lt_le_dec i n1) as [X|X]; [apply D1; lia|].
  replace (a + i) with (a + n1 + (i - n1)) by lia. apply D2. lia.
Qed.

(* [comment removed for export] *)
Lemma rd_step LB cr (fx fx1 : FPState) R R1 (pc pc1 : Z) M M1 model K (sp os : Z) :
  hi_heap HI LB cr M (m_vmmaps model) -> m_halted model = None -> m_vm_lazy model = [] -> 0x7fff80000000 <= hl_sptop L ->
  hl_ceil L <= sp - 48 -> sp <= os -> os + 296 <= hl_sptop L ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) -> mem_grows M M1 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (os + 256 <= i < os + 256 + 40) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (hi_heap HI LB cr M1 (m_vmmaps model) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof.
  intros HH Mh Ml TOP H1 H1' H2 MS MG FRZ KONT.
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R pc R1 pc1 M1
           (fun a => (sp - 48 <= a < sp - 48 + 48) \/ (os + 256 <= a < os + 256 + 40)) K HH Mh Ml TOP MS MG).
  - intros a Ha N. apply FRZ; [exact Ha| |]; intros X; apply N; [left|right]; exact X.
  - intros a Pa. unfold PMK.cwr. left. lia.
  - intros a. apply PMK.or_dec; apply PMK.rng_dec.
  - exact KONT.
Qed.
Lemma rd_ek LB (sp os : Z) W M M1 :
  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (os + 256 <= i < os + 256 + 40) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  L5C.stk (hl_sptop L) M sp 20480 -> PMFR.brange L LB -> (forall a, os + 256 <= a < os + 296 -> PMK.inW W a) ->
  PMK.ek L LB sp 20480 W M M1.
Proof.
  intros FRZ STK BR INF.
  apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W M M1
           (fun a => (sp - 48 <= a < sp - 48 + 48) \/ (os + 256 <= a < os + 256 + 40)) ltac:(intros a Ha N; apply FRZ; [exact Ha| |]; intros X; apply N; [left|right]; exact X)
           STK (PMFR.brange_hi L LB BR)).
  intros a [Pa|Pa]; [left; lia| right; apply INF; lia].
Qed.
(* [comment removed for export] *)
Lemma rd_ek_cpy LB (sp dst n : Z) W M M1 :
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + n) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  L5C.stk (hl_sptop L) M sp 20480 -> PMFR.brange L LB -> (forall a, dst <= a < dst + n -> PMK.inW W a) ->
  PMK.ek L LB sp 20480 W M M1.
Proof.
  intros FRZ STK BR INF.
  apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W M M1 (fun a => dst <= a < dst + n) FRZ STK (PMFR.brange_hi L LB BR)).
  intros a Pa. right. apply INF. exact Pa.
Qed.

Local Ltac tr64 M0 AG := lazymatch goal with |- L5.u64_at ?sg ?M2 ?a ?v =>
  let X := fresh "X" in assert (X : L5.u64_at sg M0 a v) by PMK.gmem;
  apply (L5C.u64_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.

Theorem src_read_okG : PGS.fill_buffer_specG RSEGS AD L HI -> PMPSS.xsgetn_spec L HI -> PGS.src_read_specG RSEGS AD L HI.
Proof.
  intros FB XS. unfold PGS.src_read_specG, PGS.src_specG.
  intros O OK fx R M model K OB LBX cr sp r src str sm Wextra HH MOK K0 ENT SPLO A10 ARGS WX PA IA BASE INCS KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
  pose proof (PGS.oo_lay _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & AL36 & AL37 & LY6 & LYD).
  pose proof (PGS.oo_src _ _ _ _ _ OK M src OB PA) as (PSRC & PNI & SDEF).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  assert (F1 : sp <= os /\ sp <= ois /\ os + 296 <= hl_sptop L /\ ois + 272 <= hl_sptop L /\ (os + 296 <= ois \/ ois + 272 <= os)) by (clear - SPLO LY1 LY2 LY3 LY4 LY5 LYD; lia).
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEFs). pose proof RAok as (Hr1 & Hr2).
  destruct ARGS as (p & k & A11 & A12 & Hk & DST). destruct WX as (p' & k' & A11' & A12' & Hp' & Hk' & ->).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5K.rl11 in A11, A11'. rewrite L5K.rl12 in A12, A12'.
  change (PMSP.pm_scr 4) with 20480 in *. unfold PM.CHUNK in *.
  assert (SC0 : 0 <= 20480) by lia.
  set (LB := PM.src_own src ++ OB ++ LBX) in *.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
  assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr M _ HH).
  pose proof (L5C.stk_writable RSEGS _ M sp 20480 STK) as WR.
  destruct src as [qc de rem]. destruct sm as [g eg st].
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  destruct (BR qc 16384 QIN) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4.
  destruct PSRC as (S240 & S248 & S256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & QM16 & DCH & _).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  assert (WF : L5.writable RSEGS M (os + 256) 40).
  { apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M os 296); [exact SDEF|lia|lia]|lia|lia]. }
  set (WS := PGS.W_srcfG os ois ++ [(qc, 16384)]).
  assert (WSE : PGS.W_srcG os ois (PM.SRC qc de rem) = WS) by reflexivity. rewrite WSE in KONT. clear WSE.
  assert (WCs : forall a, PMK.inW WS a -> (os + 256 <= a < os + 296) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384)).
  { intros a (r0 & Hin & Hr). unfold WS, PGS.W_srcfG in Hin. cbn [app] in Hin.
    unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia. }
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as B19.
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (REMB : 0 <= rem <= 16384) by lia.
  assert (DEB : qc <= de <= qc + 16384) by lia.
  pose proof (PMPK.iss_size_lt RSEGS AD M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
  pose proof IA as (I0 & IDEF & _ & I16 & _ & _ & I40 & _ & _ & _ & _ & _ & IIOS & _ & IE2).
  destruct IIOS as (_ & J32 & J36 & J40 & _ & _ & JD & _ & JST).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios AD PnLayoutS_u.ADDR_S] in *.
  (* [comment removed for export] *)
  assert (DWX : (sp <= p /\ p + k <= lo) \/ PGS.ow_win O M (PM.SRC qc de rem) OB p k).
  { destruct DST as [(D1 & D2 & D3 & D4)|DW]; [left; split; [exact D1| exact D2]| right; exact DW]. }
  assert (DF : 4096 <= p /\ p + k <= 2 ^ 47 /\ L5.defined M p k /\ (forall a, p <= a < p + k -> PMK.cwr L LB a)
     /\ (forall a, p <= a < p + k -> ~ (sp - 20480 <= a < sp) /\ ~ (os <= a < os + 296) /\ ~ (ois <= a < ois + 272)
           /\ ~ (qc <= a < qc + 16384) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1)))
     /\ (k = 16384 -> PGS.in_blk OB p k)
     /\ (sp <= p \/ PGS.in_blk OB p k)
     /\ (forall a, p <= a < p + k -> ~ (hl_img_lo L <= a < hl_img_hi L))).
  { pose proof (PMK.kl_img RSEGS L KL) as KI. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in KI |- *.
    assert (STRB : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> q1 + c1 <= hl_ceil L).
    { intros c1 n1 q1 ->. assert (SIN : In (q1, c1) LB) by (apply SINC; left; reflexivity). destruct (BR _ _ SIN) as (_ & _ & Z4). exact Z4. }
    destruct DST as [(D1 & D2 & D3 & D4)|DW].
    - split; [lia|]. split; [lia|]. split; [exact D4|]. split.
      { intros a Ha. apply (PMK.cwr_stack L LB M sp 20480 a STK). lia. }
      split; [|split; [intros E; exfalso; lia| split; [left; lia| intros a Ha; unfold hl_ceil in *; lia]]].
      intros a Ha. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold hl_ceil in *; lia|].
      intros c1 n1 q1 E. pose proof (STRB c1 n1 q1 E). unfold hl_ceil in *. lia.
    - destruct (PGS.oo_win _ _ _ _ _ OK M (PM.SRC qc de rem) OB p k PA DW) as (W0 & WD & [(B & m & BIN & WB1 & WB2)|(W1 & W2 & WL1 & WL2 & WL3 & WL4 & WL5)]).
      + assert (TIN : In (B, m) LB) by (unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact BIN).
        destruct (BR _ _ TIN) as (T0 & T1 & T4). unfold hl_ceil in T4.
        assert (NQ : B <> qc).
        { intros E. subst B. apply (PMPK.fst_neq_app [(qc, 16384)] (OB ++ LBX) qc 16384 qc m); [exact NDL| left; reflexivity| apply in_or_app; left; exact BIN| reflexivity]. }
        destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ B m qc 16384 HH TIN QIN NQ) as [AQ|AQ].
        all: split; [lia|]; split; [lia|]; split; [exact WD|]; split; [intros a Ha; apply (PMK.cwr_block L LB B m a TIN); lia|].
        all: split; [|split; [intros _; exists B, m; split; [exact BIN| lia]| split; [right; exists B, m; split; [exact BIN| lia]|]]];
             [| intros a Ha; rewrite (ly_img_lo L LY), (ly_img_hi L LY) in T1; clear - Ha WB1 WB2 T1; lia].
        all: intros a Ha; split; [clear - Ha WB2 T4 SLO; unfold hl_ceil in *; lia|]; split; [clear - Ha WB2 T4 SLO F1; unfold hl_ceil in *; lia|];
             split; [clear - Ha WB2 T4 SLO F1; unfold hl_ceil in *; lia|]; split; [clear - Ha WB1 WB2 AQ; lia|].
        all: intros c1 n1 q1 E; assert (SIN : In (q1, c1) LBX) by (apply INCS; rewrite E; left; reflexivity).
        all: assert (NE : B <> q1) by (apply (PMPK.fst_neq_app ((qc, 16384) :: OB) LBX B m q1 c1); [exact NDL| right; exact BIN| exact SIN]).
        all: destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ B m q1 c1 HH TIN (SINC _ ltac:(rewrite E; left; reflexivity)) NE) as [AS|AS]; clear - Ha WB1 WB2 AS; lia.
      + unfold PM.CHUNK in WL3. split; [lia|]. split; [lia|]. split; [exact WD|]. split.
        { intros a Ha. apply (PMK.cwr_stack L LB M sp 20480 a STK). lia. }
        split; [|split; [intros E; exfalso; lia| split; [left; lia| intros a Ha; unfold hl_ceil in *; lia]]].
        intros a Ha. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold hl_ceil in *; lia|].
        intros c1 n1 q1 E. pose proof (STRB c1 n1 q1 E). unfold hl_ceil in *. lia. }
  destruct DF as (DP0 & DP1 & DD & DCW & DX & D16K & DWH & DXI).
  assert (QI : forall a, qc <= a < qc + 16384 -> ~ (65536 <= a < 962560)).
  { rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. intros a Ha. clear - Ha Q1. lia. }
  clear DST Q1.
  assert (NDF : forall i, (sp - 20480 <= i < sp) \/ (os <= i < os + 296) \/ (ois <= i < ois + 272) \/ (qc <= i < qc + 16384) -> ~ (p <= i < p + k)).
  { intros i H Hd. destruct (DX i Hd) as (Y1 & Y2 & Y3 & Y4 & _). clear - H Y1 Y2 Y3 Y4. lia. }
  assert (NDR : forall a n, (sp - 20480 <= a /\ a + n <= sp) \/ (os <= a /\ a + n <= os + 296) \/ (ois <= a /\ a + n <= ois + 272) ->
                forall i, a <= i < a + n -> ~ (p <= i < p + k)).
  { intros a n H i Hi. apply NDF. clear - H Hi. lia. }
  assert (pk : p' = p /\ k' = k).
  { rewrite A11 in A11'. rewrite A12 in A12'. apply (f_equal bv_unsigned) in A11', A12'. rewrite !L5.unsigned_lit in A11', A12' by lia. split; congruence. }
  destruct pk as (-> & ->). clear A11' A12'.
  set (WA := WS ++ [(p, k)]).
  assert (WCA : forall a, PMK.inW WA a -> (os + 256 <= a < os + 296) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384) \/ (p <= a < p + k)).
  { intros a I. unfold WA in I. destruct I as (r0 & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    - assert (X : PMK.inW WS a) by (exists r0; split; assumption). apply WCs in X. lia.
    - destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (INWf : forall a, os + 256 <= a < os + 296 -> PMK.inW WA a).
  { intros a Ha. unfold WA, WS, PGS.W_srcfG. cbn [app]. apply PMK.inW_here. lia. }
  assert (INWd : forall a, p <= a < p + k -> PMK.inW WA a).
  { intros a Ha. unfold WA. apply PMK.inW_app_r. apply PMK.inW_here. exact Ha. }
  assert (INWg : forall a, ois + 40 <= a < ois + 48 -> PMK.inW WA a).
  { intros a Ha. unfold WA, WS, PGS.W_srcfG. cbn [app]. apply PMK.inW_next. apply PMK.inW_here. lia. }
  assert (INWs : forall a, ois + 152 <= a < ois + 156 -> PMK.inW WA a).
  { intros a Ha. unfold WA, WS, PGS.W_srcfG. cbn [app]. do 2 apply PMK.inW_next. apply PMK.inW_here. lia. }
  unfold PMSP.cfg. cbn [pa_src_read AD PnLayoutS_u.ADDR_S].
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
  assert (OWU : forall (M3 : word -> option byte) (de' rem' : Z), L5C.hpres L LB sp 20480 WA M M3 ->
      L5.u64_at RSEGS M3 (os + 264) qc -> L5.u64_at RSEGS M3 (os + 272) 16384 ->
      L5.u64_at RSEGS M3 (os + 280) de' -> L5.u64_at RSEGS M3 (os + 288) rem' ->
      qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
      PGS.ow_at O M3 (PM.SRC qc de' rem') OB).
  { intros M3 de' rem' HP3 C264 C272 C280 C288 Q1' Q2' Q3'.
    assert (AGH : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW WA i) -> L5C.agree_on M M3 a n).
    { intros a n H1 H2 N. apply (PMPK.ag_hi RSEGS L KL LB sp 20480 WA M M3 (PMK.ek_of_hpres L LB sp 20480 WA M M3 HP3) STK SC0 a n H1 H2 N). }
    assert (DKH : forall a n, sp <= a -> a + n <= 2 ^ 64 -> PMPK.dkr M M3 a n).
    { intros a n H1 H2. apply (PMPK.dkr_hpres_hi RSEGS L KL LB sp 20480 WA M M3 a n HP3 STK SC0 H1 H2). }
    assert (DKB : forall B m, In (B, m) LB -> PMPK.dkr M M3 B m).
    { intros B m Hin. apply (PMPK.dkr_hpres_blk RSEGS L KL LB sp 20480 WA M M3 B m HP3 Hin BR). lia. }
    apply (PGS.oo_upd _ _ _ _ _ OK LBX sp 20480 [(p, k)] M M3 (PM.SRC qc de rem) (PM.SRC qc de' rem') OB cr (m_vmmaps model) SPLO PA HH OWA OWB).
    - constructor; [| constructor]. cbn [fst snd]. destruct DWX as [(DW1 & DW2)|DW]; [left; split; [left; exact DW2|] | right; exact DW].
      intros B m Hin. right. assert (HB : In (B, m) LB) by (unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
      destruct (BR _ _ HB) as (_ & _ & Z4). unfold hl_ceil in Z4. clear - Z4 SLO DW1. lia.
    - exact HP3.
    - unfold PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem]. unfold PM.CHUNK.
      split; [apply (L5C.u64_at_agree RSEGS M M3); [apply AGH; [lia|lia|]; intros i Hi I; apply WCA in I; destruct I as [I|[I|[I|[I|I]]]]; [lia|lia|lia|clear - Hi I Q4 SLO F1; unfold hl_ceil in *; lia| apply (NDF i); [lia| exact I]]|lia|lia| exact S240]|].
      split; [apply (L5C.u64_at_agree RSEGS M M3); [apply AGH; [lia|lia|]; intros i Hi I; apply WCA in I; destruct I as [I|[I|[I|[I|I]]]]; [lia|lia|lia|clear - Hi I Q4 SLO F1; unfold hl_ceil in *; lia| apply (NDF i); [lia| exact I]]|lia|lia| exact S248]|].
      split; [apply (PMPK.defined_dkr M M3 (os + 256) 8 (DKH (os + 256) 8 ltac:(lia) ltac:(lia)) S256)|].
      split; [exact C264|]. split; [exact C272|]. split; [exact C280|]. split; [exact C288|].
      split; [exact Q1'|]. split; [exact Q2'|]. split; [exact Q3'|]. split; [exact QM16|].
      split; [apply (PMPK.defined_dkr M M3 qc 16384 (DKB qc 16384 QIN) DCH)|]. split; exact I.
    - reflexivity. }
  (* [comment removed for export] *)
  assert (FIN : forall (fx3 : FPState) (R3 : bvmap 5 word) (M3 : word -> option byte) (de' rem' g' st' d : Z),
      getr R3 (PMK.reg 1) = getr R (PMK.reg 1) ->
      (forall x, In x PMK.cs_all -> getr R3 (PMK.reg x) = getr R (PMK.reg x)) ->
      getr R3 (PMK.reg 10) = Z_to_bv 64 d ->
      L5.u64_at RSEGS M3 (os + 264) qc -> L5.u64_at RSEGS M3 (os + 272) 16384 ->
      L5.u64_at RSEGS M3 (os + 280) de' -> L5.u64_at RSEGS M3 (os + 288) rem' ->
      qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
      L5.u64_at RSEGS M3 (ois + 40) g' -> L5.u32_at RSEGS M3 (ois + 152) st' ->
      g <= g' <= eg -> (st' = 0 \/ st' = 2) -> (st = 2 -> st' = 2) ->
      0 <= d <= k -> (rem + (eg - g)) - (rem' + (eg - g')) = d ->
      (1 <= rem -> 1 <= d) -> (d = 0 -> rem' = 0 /\ st' = 2) ->
      PMK.ek L LB sp 20480 WA M M3 -> PMK.dk L LB sp 20480 M M3 -> L5C.stk (hl_sptop L) M3 sp 20480 ->
      hi_heap HI LB cr M3 (m_vmmaps model) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0x372c8 M3 model) K).
  { intros fx3 R3 M3 de' rem' g' st' d E1 E2 E10 C264 C272 C280 C288 Q1' Q2' Q3' CG CS Hg Hst Hst2 Hd Hcons HR1 HR0 EK DK STK3 HH3.
    unfold PMSP.cfg.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
    { apply (PMK.ret_to RSEGS fx3 R3 M3 0x372c8 W_365d8 r F_365d8 eq_refl D_365d8); [rewrite E1; exact Rra| lia| exact Hr2]. }
    assert (HPf : L5C.hpres L LB sp 20480 WA M M3).
    { apply (PMK.hpres_of L LB sp 20480 WA M M3 EK); [destruct STK3 as (_ & _ & _ & _ & D3); exact D3| exact DK]. }
    assert (AGH : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW WA i) -> L5C.agree_on M M3 a n).
    { intros a n H1 H2 N. apply (PMPK.ag_hi RSEGS L KL LB sp 20480 WA M M3 EK STK SC0 a n H1 H2 N). }
    assert (DKH : forall a n, sp <= a -> a + n <= 2 ^ 64 -> PMPK.dkr M M3 a n).
    { intros a n H1 H2. apply (PMPK.dkr_hpres_hi RSEGS L KL LB sp 20480 WA M M3 a n HPf STK SC0 H1 H2). }
    assert (DKB : forall B m, In (B, m) LB -> PMPK.dkr M M3 B m).
    { intros B m Hin. apply (PMPK.dkr_hpres_blk RSEGS L KL LB sp 20480 WA M M3 B m HPf Hin BR). lia. }
    assert (NWI : forall a n, (ois <= a /\ a + n <= ois + 40) \/ (ois + 48 <= a /\ a + n <= ois + 152) \/ (ois + 156 <= a /\ a + n <= ois + 272) ->
                  forall i, a <= i < a + n -> ~ PMK.inW WA i).
    { intros a n H i Hi I. apply WCA in I.
      destruct I as [I|[I|[I|[I|I]]]]; [clear - Hi I H Q4 SLO F1 STOP; unfold hl_ceil in *; lia ..|].
      destruct (DX i I) as (_ & _ & Y3 & _). clear - Hi H Y3. lia. }
    assert (DD3 : L5.defined M3 p k).
    { destruct DWH as [W1|(B & m & BIN & W1 & W2)].
      - apply (PMPK.defined_dkr M M3 p k (DKH p k ltac:(lia) ltac:(lia)) DD).
      - assert (TIN : In (B, m) LB) by (unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact BIN).
        apply (PMPK.defined_dkr M M3 p k); [apply (PMPK.dkr_sub M M3 B m p k (DKB B m TIN)); lia| exact DD]. }
    apply (KONT fx3 R3 M3 (PM.SRC qc de' rem') (PM.STRM g' eg st')).
    + apply PMK.preserved_by_index. exact E2.
    + exact (OWU M3 de' rem' HPf C264 C272 C280 C288 Q1' Q2' Q3').
    + apply (PMPK.iss_upd RSEGS AD M M3 (ois) str (PM.STRM g eg st) g' st' IA); cbn [PM.sm_g PM.sm_eg PM.sm_st].
      * lia.
      * lia.
      * apply AGH; [lia|lia|]. apply NWI; lia.
      * apply AGH; [lia|lia|]. apply NWI; lia.
      * apply AGH; [lia|lia|]. apply NWI; lia.
      * apply DKH; lia.
      * apply DKH; lia.
      * intros c1 n1 q1 ->. apply DKB. apply SINC. left. reflexivity.
      * exact CG.
      * exact CS.
      * lia.
      * exact Hst.
    + unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|].
      split; [lia|]. split; [exact Hst2| lia].
    + unfold PMPS.read_res, PMSP.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. exists p, k, d.
      rewrite L5K.rl11, L5K.rl12, L5K.rl10. split; [exact A11|]. split; [exact A12|]. split; [lia|]. split; [unfold PM.CHUNK; lia|].
      split; [exact E10|]. split; [exact Hd|].
      split; [exact Hcons|]. split; [apply (L5.defined_sub M3 p k); [exact DD3|lia|lia]|]. split; [exact HR1| exact HR0].
    + exact HPf.
    + exact HH3. }
  (* [comment removed for export] *)
  assert (CPART : forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (len1 c g2 st2 : Z),
      getr R2 (PMK.reg 10) = Z_to_bv 64 c -> getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr R2 (PMK.reg 8) = Z_to_bv 64 (os) ->
      getr R2 (PMK.reg 9) = Z_to_bv 64 len1 -> getr R2 (PMK.reg 18) = Z_to_bv 64 (k - len1) -> getr R2 (PMK.reg 19) = Z_to_bv 64 p ->
      (forall x, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (PMK.reg x) = getr R (PMK.reg x)) ->
      L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) -> L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
      L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
      L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) ->
      L5.u64_at RSEGS M2 (os + 264) qc -> L5.u64_at RSEGS M2 (os + 272) 16384 ->
      L5.u64_at RSEGS M2 (os + 280) qc -> L5.u64_at RSEGS M2 (os + 288) 0 -> L5.defined M2 (os + 256) 40 ->
      L5.defined M2 qc 16384 ->
      L5.u64_at RSEGS M2 (ois + 40) g2 -> L5.u32_at RSEGS M2 (ois + 152) st2 ->
      len1 = rem -> len1 < k -> k - len1 <= 16383 -> 0 <= c <= 16384 -> g2 = g + c -> g2 <= eg -> (st2 = 0 \/ st2 = 2) -> (st = 2 -> st2 = 2) -> (c = 0 -> st2 = 2) ->
      L5.defined M2 p k ->
      PMK.ek L LB sp 20480 WA M M2 -> PMK.dk L LB sp 20480 M M2 -> L5C.stk (hl_sptop L) M2 sp 20480 ->
      hi_heap HI LB cr M2 (m_vmmaps model) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x3717c M2 model) K).
  { intros fx2 R2 M2 len1 c g2 st2 Y10 Y2 Y8 Y9 Y18 Y19 KS2 C8 C16 C24 C32 C40 D264 D272 D280 D288 D256 DQ CG CS Hl1 Hl1k Hl1k' Hc Hg2 Hg2e Hst2 Hst22 Hc0 DP2 EK2 DK2 STK2 HH2.
    pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
    assert (WF2 : L5.writable RSEGS M2 (os + 256) 40) by (apply (L5C.writable_of_defined RSEGS); [exact D256|lia|lia]).
    assert (DE8 : L5.defined M2 (os + 256) 8) by (apply (L5.defined_sub M2 _ 40 _ 8 D256); lia).
    destruct (Z.eq_dec c 0) as [E0|N0].
    - (* [comment removed for export] *)
      subst c.
      LeanFeed.pfeed P (PMSRDP.srC0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => qc | 36%nat => os | 37%nat => p | 38%nat => k - len1 | 39%nat => len1
                 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                 | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
      PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T10 & T18 & T19 & E288 & E264 & E272 & E280 & _)); PMK.pvz_clrT.
      rewrite PMPK.word_id in T1, T8, T9, T18, T19.
      apply (rd_step LB cr fx2 fx3 R2 R3 0x3717c 0x372c8 M2 M3 model K sp os HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS3 MG3 FRZ3).
      intros HH3.
      apply (FIN fx3 R3 M3 qc 0 g2 st2 len1).
      + exact T1.
      + intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite T2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
      + exact T10.
      + exact E264.
      + exact E272.
      + exact E280.
      + exact E288.
      + lia.
      + lia.
      + lia.
      + apply (L5C.u64_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact CG].
      + apply (PMF.u32_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact CS].
      + lia.
      + exact Hst2.
      + exact Hst22.
      + lia.
      + lia.
      + lia.
      + intros _. split; [reflexivity| apply Hc0; reflexivity].
      + apply (PMK.ek_trans L LB sp 20480 WA M M2 M3 EK2). apply (rd_ek LB sp os WA M2 M3 FRZ3 STK2 BR INWf).
      + apply (PMK.dk_trans L LB sp 20480 M M2 M3 DK2). apply (PMK.dk_grows L LB sp 20480 M2 M3 MG3).
      + apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2).
      + exact HH3.
    - (* [comment removed for export] *)
      set (len2 := Z.min c (k - len1)).
      assert (HEADC : exists fx3 R3 M3, msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x3717c) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0xab480) M3 (seg_rom RSEGS))
                /\ mem_grows M2 M3
                /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (os + 256 <= i < os + 256 + 40) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
                /\ (forall x, In x [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
                /\ getr R3 (PMK.reg 1) = Z_to_bv 64 225712 /\ getr R3 (PMK.reg 10) = Z_to_bv 64 (p + len1) /\ getr R3 (PMK.reg 11) = Z_to_bv 64 qc
                /\ getr R3 (PMK.reg 12) = Z_to_bv 64 len2 /\ getr R3 (PMK.reg 18) = Z_to_bv 64 len2
                /\ L5.u64_at RSEGS M3 (os + 288) c /\ L5.u64_at RSEGS M3 (os + 264) qc /\ L5.u64_at RSEGS M3 (os + 272) 16384
                /\ L5.u64_at RSEGS M3 (os + 280) qc
                /\ L5.u64_at RSEGS M3 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) /\ L5.u64_at RSEGS M3 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
                /\ L5.u64_at RSEGS M3 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS M3 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
                /\ L5.u64_at RSEGS M3 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))).
      { destruct (Z_lt_le_dec (k - len1) c) as [CLT|CGE].
        - assert (len2 = k - len1) as -> by (clear - CLT; unfold len2; lia).
          LeanFeed.pfeed P (PMSRDP.srClt_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => os | 37%nat => p | 38%nat => k - len1 | 39%nat => len1
                     | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                     | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
          PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & E288 & E264 & E272 & E280 & _ & S8 & S16 & S24 & S32 & S40)); PMK.pvz_clrT.
          exists fx3, R3, M3. split; [exact MS3|]. split; [exact MG3|]. split; [exact FRZ3|].
          split. { intros x Hx. apply KS3. revert x Hx. apply (PMPK.sub_in PMSRDP.KS_srClt). vm_compute. reflexivity. }
          split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|].
          split; [rewrite (KS3 18%nat) by PMK.inl; exact Y18|].
          split; [exact E288|]. split; [exact E264|]. split; [exact E272|]. split; [exact E280|].
          split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32| exact S40].
        - assert (len2 = c) as -> by (clear - CGE; unfold len2; lia).
          LeanFeed.pfeed P (PMSRDP.srCge_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => os | 37%nat => p | 38%nat => k - len1 | 39%nat => len1
                     | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                     | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
          PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & T18 & E288 & E264 & E272 & E280 & _ & S8 & S16 & S24 & S32 & S40)); PMK.pvz_clrT.
          exists fx3, R3, M3. split; [exact MS3|]. split; [exact MG3|]. split; [exact FRZ3|].
          split. { intros x Hx. apply KS3. revert x Hx. apply (PMPK.sub_in PMSRDP.KS_srCge). vm_compute. reflexivity. }
          split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|]. split; [exact T18|].
          split; [exact E288|]. split; [exact E264|]. split; [exact E272|]. split; [exact E280|].
          split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32| exact S40]. }
      destruct HEADC as (fx3 & R3 & M3 & MS3 & MG3 & FRZ3 & KS3 & T1 & T10 & T11 & T12 & T18 & E288 & E264 & E272 & E280 & S8 & S16 & S24 & S32 & S40).
      assert (L2R : 1 <= len2 <= 16383 /\ len2 <= c /\ len2 <= k - len1 /\ (len2 = k - len1 \/ len2 = c)) by (clear - N0 Hc Hl1k Hl1k'; unfold len2; lia).
      destruct L2R as (L2a & L2b & L2c & L2d).
      apply (rd_step LB cr fx2 fx3 R2 R3 0x3717c 0xab480 M2 M3 model K sp os HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS3 MG3 FRZ3).
      intros HH3.
      assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480) by (apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2)).
      (* [comment removed for export] *)
      apply (rd_cpy LB cr fx3 R3 M3 model K (p + len1) qc len2 225712 HH3 Mh Ml ltac:(lia) T10 T11 T12 T1 ltac:(split; [lia| reflexivity])).
      { lia. } { lia. } { lia. } { lia. } { lia. }
      { destruct (apart_pt (p + len1) len2 qc 16384 ltac:(lia) ltac:(lia)) as [X|X]; [| left; exact X| right; lia].
        intros a Ha. destruct (DX a ltac:(lia)) as (_ & _ & _ & Y4 & _). exact Y4. }
      { apply (L5.defined_grows M2 M3 _ _ MG3). apply (L5.defined_sub M2 p k); [exact DP2|lia|lia]. }
      { apply (L5.defined_grows M2 M3 _ _ MG3). apply (L5.defined_sub M2 qc 16384); [exact DQ|lia|lia]. }
      { intros a Ha. apply DCW. lia. }
      intros R4 M4 MG4 FRZ4 _ KS4 HH4.
      assert (AG4 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ (p <= i < p + k)) -> L5C.agree_on M3 M4 a n).
      { intros a n H1 H2 N i Hi. apply FRZ4; [lia|]. intros X. apply (N i Hi). clear - X L2a L2c Hl1k DP0 Hl1 REMB. lia. }
      assert (ND : forall a n, (sp - 20480 <= a /\ a + n <= sp) \/ (os <= a /\ a + n <= os + 296) \/ (ois <= a /\ a + n <= ois + 272) ->
                   forall i, a <= i < a + n -> ~ (p <= i < p + k)).
      { intros a n H i Hi. apply NDF. clear - H Hi. lia. }
      assert (S8' : L5.u64_at RSEGS M4 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact S8]).
      assert (S16' : L5.u64_at RSEGS M4 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact S16]).
      assert (S24' : L5.u64_at RSEGS M4 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact S24]).
      assert (S32' : L5.u64_at RSEGS M4 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact S32]).
      assert (S40' : L5.u64_at RSEGS M4 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact S40]).
      assert (E288' : L5.u64_at RSEGS M4 (os + 288) c) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact E288]).
      assert (E264' : L5.u64_at RSEGS M4 (os + 264) qc) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact E264]).
      assert (E272' : L5.u64_at RSEGS M4 (os + 272) 16384) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact E272]).
      assert (E280' : L5.u64_at RSEGS M4 (os + 280) qc) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact E280]).
      assert (WR4 : L5.writable RSEGS M4 (sp - 20480) 20480).
      { apply (L5.writable_grows RSEGS M3 M4 _ _ MG4). apply (L5.writable_grows RSEGS M2 M3 _ _ MG3). exact WR2. }
      assert (WF4 : L5.writable RSEGS M4 (os + 256) 40).
      { apply (L5.writable_grows RSEGS M3 M4 _ _ MG4). apply (L5.writable_grows RSEGS M2 M3 _ _ MG3). exact WF2. }
      assert (DE84 : L5.defined M4 (os + 256) 8).
      { apply (L5.defined_grows M3 M4 _ _ MG4). apply (L5.defined_grows M2 M3 _ _ MG3). exact DE8. }
      (* [comment removed for export] *)
      LeanFeed.pfeed P (PMSRDP.srD_conc fx3 R4 M4 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 35%nat => qc | 36%nat => os | 37%nat => p
                 | 38%nat => len2 | 39%nat => len1
                 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                 | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
      PMK.pvz_hg ltac:(idtac; destruct P as (fx5 & R5 & M5 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG5 & _ & FRZ5 & MS5 & KS5 & U1 & U2 & U8 & U9 & U10 & U11 & U18 & U19 & F288 & F280 & F264 & F272 & _)); PMK.pvz_clrT.
      rewrite PMPK.word_id in U1, U8, U9, U18, U19.
      apply (rd_step LB cr fx3 fx5 R4 R5 0x371b0 0x372c8 M4 M5 model K sp os HH4 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS5 MG5 FRZ5).
      intros HH5.
      assert (STK4 : L5C.stk (hl_sptop L) M4 sp 20480) by (apply (PMK.stk_grows L M3 M4 sp 20480 MG4 STK3)).
      assert (AG25 : forall a n, (ois <= a /\ a + n <= ois + 272) -> L5C.agree_on M2 M5 a n).
      { intros a n H. apply (L5C.agree_on_trans M2 M3 M5); [intros i Hi; apply FRZ3; lia|].
        apply (L5C.agree_on_trans M3 M4 M5); [apply AG4; [lia|lia| apply ND; lia]|]. intros i Hi; apply FRZ5; lia. }
      apply (FIN fx5 R5 M5 (qc + len2) (c - len2) g2 st2 (len2 + len1)).
      + exact U1.
      + intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite U2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
      + exact U10.
      + exact F264.
      + exact F272.
      + exact F280.
      + exact F288.
      + lia.
      + lia.
      + lia.
      + apply (L5C.u64_at_agree RSEGS M2 M5); [apply AG25; lia|lia|lia| exact CG].
      + apply (PMF.u32_at_agree RSEGS M2 M5); [apply AG25; lia|lia|lia| exact CS].
      + lia.
      + exact Hst2.
      + exact Hst22.
      + lia.
      + destruct L2d as [X|X]; rewrite X; lia.
      + lia.
      + intros X. exfalso. lia.
      + apply (PMK.ek_trans L LB sp 20480 WA M M2 M5 EK2). apply (PMK.ek_trans L LB sp 20480 WA M2 M3 M5); [apply (rd_ek LB sp os WA M2 M3 FRZ3 STK2 BR INWf)|].
        apply (PMK.ek_trans L LB sp 20480 WA M3 M4 M5); [apply (rd_ek_cpy LB sp (p + len1) len2 WA M3 M4 FRZ4 STK3 BR); intros a Ha; apply INWd; lia|].
        apply (rd_ek LB sp os WA M4 M5 FRZ5 STK4 BR INWf).
      + apply (PMK.dk_trans L LB sp 20480 M M2 M5 DK2). apply (PMK.dk_grows L LB sp 20480 M2 M5).
        apply (mem_grows_trans M2 M3 M5 MG3). apply (mem_grows_trans M3 M4 M5 MG4 MG5).
      + apply (PMK.stk_grows L M4 M5 sp 20480 MG5 STK4).
      + exact HH5. }
  (* [comment removed for export] *)
  assert (FILLC : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (len1 : Z),
      getr R1 (PMK.reg 1) = Z_to_bv 64 225660 -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr R1 (PMK.reg 8) = Z_to_bv 64 (os) ->
      getr R1 (PMK.reg 9) = Z_to_bv 64 len1 -> getr R1 (PMK.reg 10) = Z_to_bv 64 (os) -> getr R1 (PMK.reg 11) = Z_to_bv 64 qc ->
      getr R1 (PMK.reg 12) = Z_to_bv 64 16384 -> getr R1 (PMK.reg 18) = Z_to_bv 64 (k - len1) -> getr R1 (PMK.reg 19) = Z_to_bv 64 p ->
      (forall x, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x)) ->
      L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
      L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
      L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) ->
      L5.u64_at RSEGS M1 (os + 264) qc -> L5.u64_at RSEGS M1 (os + 272) 16384 ->
      L5.u64_at RSEGS M1 (os + 280) qc -> L5.u64_at RSEGS M1 (os + 288) 0 ->
      len1 = rem -> len1 < k -> k - len1 <= 16383 ->
      (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp) -> ~ (os + 256 <= i < os + 296) -> ~ (p <= i < p + k) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
      mem_grows M M1 ->
      hi_heap HI LB cr M1 (m_vmmaps model) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x382d4 M1 model) K).
  { intros fx1 R1 M1 len1 X1 X2 X8 X9 X10 X11 X12 X18 X19 KS1 C8 C16 C24 C32 C40 C264 C272 C280 C288 Hl1 Hl1k Hl1k' FRZ1 MG1 HH1.
    assert (AG1 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 48 \/ sp <= a) -> (a + n <= os + 256 \/ os + 296 <= a) ->
                  (forall i, a <= i < a + n -> ~ (p <= i < p + k)) -> L5C.agree_on M M1 a n).
    { intros a n H1 H2 H3 H4 N i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H3 Hi; lia| clear - H4 Hi; lia| apply (N i Hi)]. }
    assert (ND : forall a n, (sp - 20480 <= a /\ a + n <= sp) \/ (os <= a /\ a + n <= os + 296) \/ (ois <= a /\ a + n <= ois + 272) ->
                 forall i, a <= i < a + n -> ~ (p <= i < p + k)).
    { intros a n H i Hi. apply NDF. clear - H Hi. lia. }
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (PMK.stk_grows L M M1 sp 20480 MG1 STK)).
    assert (EK1 : PMK.ek L LB sp 20480 WA M M1).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 WA M M1 (fun a => (sp - 48 <= a < sp) \/ (os + 256 <= a < os + 296) \/ (p <= a < p + k))
               ltac:(intros a Ha N; apply FRZ1; [exact Ha| | |]; intros X; apply N; [left|right; left|right; right]; exact X) STK (PMFR.brange_hi L LB BR)).
      intros a [Pa|[Pa|Pa]]; [left; lia| right; apply INWf; lia| right; apply INWd; lia]. }
    assert (PA1 : PGS.ow_at O M1 (PM.SRC qc qc 0) OB).
    { apply (OWU M1 qc 0); [| exact C264 | exact C272 | exact C280 | exact C288 | lia | lia | lia].
      apply (PMK.hpres_of L LB sp 20480 WA M M1 EK1); [destruct STK1 as (_ & _ & _ & _ & D1); exact D1| apply (PMK.dk_grows L LB sp 20480 M M1 MG1)]. }
    assert (IA1 : PM.iss_at RSEGS AD PMSP.T3 M1 (ois) str (PM.STRM g eg st)).
    { apply (PMPK.iss_upd RSEGS AD M M1 (ois) str (PM.STRM g eg st) g st IA); cbn [PM.sm_g PM.sm_eg PM.sm_st].
      - lia.
      - lia.
      - apply AG1; [lia|lia|lia|lia| apply ND; lia].
      - apply AG1; [lia|lia|lia|lia| apply ND; lia].
      - apply AG1; [lia|lia|lia|lia| apply ND; lia].
      - apply PMPK.dkr_grows. exact MG1.
      - apply PMPK.dkr_grows. exact MG1.
      - intros c1 n1 q1 _. apply PMPK.dkr_grows. exact MG1.
      - apply (L5C.u64_at_agree RSEGS M M1); [apply AG1; [lia|lia|lia|lia| apply ND; lia]|lia|lia| exact I40].
      - apply (PMF.u32_at_agree RSEGS M M1); [apply AG1; [lia|lia|lia|lia| apply ND; lia]|lia|lia| replace (ois + 152) with (ois + 120 + 32) by lia; exact J32].
      - lia.
      - exact JST. }
    assert (BASE1 : PMST.base_ok RSEGS AD M1).
    { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 WA M M1 EK1); [| | | | exact BASE].
      all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCA in I; pose proof (DXI a) as Y;
           cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S] in Ha.
      all: destruct I as [I|[I|[I|[I|I]]]].
      all: first [ clear - I Ha SLO F1 STOP; lia | apply (QI a I); clear - Ha; lia | apply (Y I); rewrite (ly_img_lo L LY), (ly_img_hi L LY); clear - Ha; lia ]. }
    assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 48) 18432).
    { apply (PMK.stk_call L M1 sp 20480 (sp - 48) 18432 STK1); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    unfold PGS.fill_buffer_specG, PGS.src_specG in FB. cbn [pa_fill_buffer AD PnLayoutS_u.ADDR_S] in FB.
    apply (FB O OK fx1 R1 M1 model K OB LBX cr (sp - 48) 225660 (PM.SRC qc qc 0) str (PM.STRM g eg st) [] HH1 MOK K0).
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
      split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
    { lia. }
    { rewrite L5K.rl10. exact X10. }
    { unfold PGS.fill_args. rewrite L5K.rl11, L5K.rl12. cbn [PM.sr_qc]. split; [exact X11| exact X12]. }
    { unfold PMSP.no_W. reflexivity. }
    { exact PA1. }
    { exact IA1. }
    { exact BASE1. } { exact INCS. }
    intros fx2 R2 M2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 HH2.
    unfold PMPS.fill_res in RES2. destruct RES2 as (-> & c & Y10 & CR & GG2 & RS0 & RS2).
    change (PMSP.pm_scr 3) with 18432 in HP2. rewrite app_nil_r in HP2.
    rewrite L5K.rl10 in Y10. unfold PM.CHUNK in CR, RS0.
    destruct sm2 as [g2 eg2 st2]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in GG2, RS0, RS2.
    assert (EKc : PMK.ek L LB (sp - 48) 18432 WS M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
    assert (SCc : 0 <= 18432) by lia.
    assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 48) 18432 WS STK1 HP2); lia).
    assert (HI2 : forall a n, sp - 48 <= a -> a + n <= sp -> L5C.agree_on M1 M2 a n).
    { intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB (sp - 48) 18432 WS M1 M2 EKc STKc SCc a n H1); [lia|]. intros i Hi I. apply WCs in I.
      clear - Hi I H1 H2 Q4 SLO F1; unfold hl_ceil in *; lia. }
    pose proof (PGS.oo_src _ _ _ _ _ OK M2 _ OB PA2) as (PSRC2 & _ & SDEF2).
    destruct PSRC2 as (_ & _ & T256 & T264 & T272 & T280 & T288 & _ & _ & _ & _ & DCH2 & _).
    cbn [PM.sr_qc PM.sr_de PM.sr_rem] in T264, T280, T288, DCH2. unfold PM.CHUNK in *.
    pose proof IA2 as (_ & _ & _ & _ & _ & _ & K40 & _ & _ & _ & _ & _ & KIOS & _ & KE2).
    destruct KIOS as (_ & L32 & _ & _ & _ & _ & _ & _ & LST). cbn [PM.sm_g PM.sm_eg PM.sm_st] in K40, L32, LST, KE2.
    unfold PMSP.src_step in STEP2. cbn [PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st] in STEP2. destruct STEP2 as (_ & E2 & _ & S2 & _).
    subst eg2.
    apply (CPART fx2 R2 M2 len1 c g2 st2).
    - exact Y10.
    - rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. exact X2.
    - rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. exact X8.
    - rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. exact X9.
    - rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. exact X18.
    - rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. exact X19.
    - intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply (PMPK.sub_in PMK.cs_all); vm_compute; reflexivity). apply KS1. exact Hx.
    - apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C8].
    - apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C16].
    - apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C24].
    - apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C32].
    - apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C40].
    - exact T264.
    - exact T272.
    - exact T280.
    - exact T288.
    - apply (L5.defined_sub M2 os 296); [exact SDEF2|lia|lia].
    - exact DCH2.
    - exact K40.
    - replace (ois + 152) with (ois + 120 + 32) by lia. exact L32.
    - exact Hl1.
    - exact Hl1k.
    - exact Hl1k'.
    - exact CR.
    - exact GG2.
    - lia.
    - exact LST.
    - exact S2.
    - intros C0. subst c. destruct JST as [J0|J2]; [destruct (RS0 J0) as (_ & ->); reflexivity| destruct (RS2 J2) as (_ & ->); reflexivity].
    - destruct DWH as [W1|(q0 & c0 & BIN & W1 & W2)].
      + apply (PMPK.defined_dkr M1 M2 p k); [apply (PMPK.dkr_hpres_hi RSEGS L KL LB (sp - 48) 18432 WS M1 M2 p k HP2 STKc SCc); lia|].
        exact (L5.defined_grows M M1 p k MG1 DD).
      + assert (TIN : In (q0, c0) LB) by (unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact BIN).
        apply (PMPK.defined_dkr M1 M2 p k); [apply (PMPK.dkr_sub M1 M2 q0 c0 p k); [apply (PMPK.dkr_hpres_blk RSEGS L KL LB (sp - 48) 18432 WS M1 M2 q0 c0 HP2 TIN BR); lia|lia|lia]|].
        exact (L5.defined_grows M M1 p k MG1 DD).
    - apply (PMK.ek_trans L LB sp 20480 WA M M1 M2 EK1).
      apply (PMK.ek_callee_in' RSEGS L KL LB LB sp 20480 (sp - 48) 18432 WA WS M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB BR)|].
      intros a I. right. unfold WA. apply PMK.inW_app_l. exact I.
    - apply (PMK.dk_trans L LB sp 20480 M M1 M2); [apply (PMK.dk_grows L LB sp 20480 M M1 MG1)|].
      apply (PMK.dk_callee L LB LB sp 20480 (sp - 48) 18432 WS M1 M2 HP2 (incl_refl _)); lia.
    - exact STK2.
    - exact HH2. }
  pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG.
  destruct (Z_le_gt_dec 1 rem) as [REM1|REM0].
  - (* [comment removed for export] *)
    set (len1 := Z.min k rem).
    assert (L1R : 1 <= len1 <= rem /\ len1 <= k /\ (len1 = k \/ len1 = rem)) by (clear - REM1 Hk; unfold len1; lia).
    destruct L1R as (L1a & L1b & L1c).
    assert (HEAD : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x370d0) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xab480) M1 (seg_rom RSEGS))
              /\ mem_grows M M1
              /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
              /\ (forall x, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
              /\ getr R1 (PMK.reg 1) = Z_to_bv 64 225560 /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48) /\ getr R1 (PMK.reg 8) = Z_to_bv 64 (os)
              /\ getr R1 (PMK.reg 9) = Z_to_bv 64 len1 /\ getr R1 (PMK.reg 10) = Z_to_bv 64 p /\ getr R1 (PMK.reg 11) = Z_to_bv 64 de
              /\ getr R1 (PMK.reg 12) = Z_to_bv 64 len1 /\ getr R1 (PMK.reg 18) = Z_to_bv 64 k /\ getr R1 (PMK.reg 19) = Z_to_bv 64 p
              /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
              /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
              /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))).
    { destruct (Z_lt_le_dec k rem) as [KLT|KGE].
      - assert (len1 = k) as -> by (clear - KLT; unfold len1; lia).
        LeanFeed.pfeed P (PMSRDP.srAlt_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os
                     | 37%nat => p | 38%nat => k | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
        PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X18 & X19 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
        exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [exact FRZ1|].
        split. { intros x Hx. apply KS1. revert x Hx. apply (PMPK.sub_in PMSRDP.KS_srAlt). vm_compute. reflexivity. }
        do 6 (split; [assumption|]). split; [rewrite (KS1 12%nat) by PMK.inl; exact A12|]. do 6 (split; [assumption|]). assumption.
      - assert (len1 = rem) as -> by (clear - KGE; unfold len1; lia).
        LeanFeed.pfeed P (PMSRDP.srAge_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os
                     | 37%nat => p | 38%nat => k | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
        PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X18 & X19 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
        exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [exact FRZ1|].
        split. { intros x Hx. apply KS1. revert x Hx. apply (PMPK.sub_in PMSRDP.KS_srAge). vm_compute. reflexivity. }
        do 13 (split; [assumption|]). assumption. }
    destruct HEAD as (fx1 & R1 & M1 & MS1 & MG1 & FRZ1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X18 & X19 & C40 & C32 & C24 & C16 & C8).
    apply (rd_step LB cr fx fx1 R R1 0x370d0 0xab480 M M1 model K sp os HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS1 MG1
             (fun i Hi N1 _ => FRZ1 i Hi N1)).
    intros HH1.
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (PMK.stk_grows L M M1 sp 20480 MG1 STK)).
    (* [comment removed for export] *)
    apply (rd_cpy LB cr fx1 R1 M1 model K p de len1 225560 HH1 Mh Ml ltac:(lia) X10 X11 X12 X1 ltac:(split; [lia| reflexivity])).
    { lia. } { lia. } { lia. } { lia. } { lia. }
    { destruct (apart_pt p len1 de len1 ltac:(lia) ltac:(lia)) as [X|X]; [| left; exact X| right; exact X].
      intros a Ha Hd. destruct (DX a ltac:(lia)) as (_ & _ & _ & Y4 & _). apply Y4. lia. }
    { apply (L5.defined_grows M M1 _ _ MG1). apply (L5.defined_sub M p k); [exact DD|lia|lia]. }
    { apply (L5.defined_grows M M1 _ _ MG1). apply (L5.defined_sub M qc 16384); [exact DCH|lia|lia]. }
    { intros a Ha. apply DCW. lia. }
    intros R2 M2 MG2 FRZ2 _ KS2 HH2.
    assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_grows L M1 M2 sp 20480 MG2 STK1)).
    assert (AG12 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ (p <= i < p + k)) -> L5C.agree_on M1 M2 a n).
    { intros a n H1 H2 N i Hi. apply FRZ2; [lia|]. intros X. apply (N i Hi). clear - X L1a L1b DP0. lia. }
    assert (AG02 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ (p <= i < p + k)) -> L5C.agree_on M M2 a n).
    { intros a n H1 H2 N. apply (L5C.agree_on_trans M M1 M2); [intros i Hi; apply FRZ1; lia| apply AG12; [lia|lia|exact N]]. }
    assert (C8' : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; [lia|lia| apply NDR; lia]|lia|lia| exact C8]).
    assert (C16' : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; [lia|lia| apply NDR; lia]|lia|lia| exact C16]).
    assert (C24' : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; [lia|lia| apply NDR; lia]|lia|lia| exact C24]).
    assert (C32' : L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; [lia|lia| apply NDR; lia]|lia|lia| exact C32]).
    assert (C40' : L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; [lia|lia| apply NDR; lia]|lia|lia| exact C40]).
    assert (F264 : L5.u64_at RSEGS M2 (os + 264) qc) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; [lia|lia| apply NDR; lia]|lia|lia| exact S264]).
    assert (F272 : L5.u64_at RSEGS M2 (os + 272) 16384) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; [lia|lia| apply NDR; lia]|lia|lia| exact S272]).
    assert (F280 : L5.u64_at RSEGS M2 (os + 280) de) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; [lia|lia| apply NDR; lia]|lia|lia| exact S280]).
    assert (F288 : L5.u64_at RSEGS M2 (os + 288) rem) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; [lia|lia| apply NDR; lia]|lia|lia| exact S288]).
    assert (F256 : L5.defined M2 (os + 256) 8).
    { apply (L5.defined_grows M M2); [apply (mem_grows_trans M M1 M2 MG1 MG2)|]. apply (L5.defined_sub M os 296); [exact SDEF|lia|lia]. }
    assert (WF2 : L5.writable RSEGS M2 (os + 256) 40).
    { apply (L5.writable_grows RSEGS M M2); [apply (mem_grows_trans M M1 M2 MG1 MG2)| exact WF]. }
    assert (WR2 : L5.writable RSEGS M2 (sp - 20480) 20480).
    { apply (L5.writable_grows RSEGS M M2); [apply (mem_grows_trans M M1 M2 MG1 MG2)| exact WR]. }
    assert (EK01 : PMK.ek L LB sp 20480 WA M M1) by (apply (rd_ek LB sp os WA M M1 (fun i Hi N1 _ => FRZ1 i Hi N1) STK BR INWf)).
    assert (EK12 : PMK.ek L LB sp 20480 WA M1 M2) by (apply (rd_ek_cpy LB sp p len1 WA M1 M2 FRZ2 STK1 BR); intros a Ha; apply INWd; lia).
    destruct (Z.eq_dec len1 k) as [EK|NK].
    + (* [comment removed for export] *)
      rewrite <- EK in X18.
      LeanFeed.pfeed P (PMSRDP.srBeq_conc fx1 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os
                   | 37%nat => p | 39%nat => len1
                   | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                   | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
      PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & E288 & E280 & E264 & E272 & _)); PMK.pvz_clrT.
      rewrite PMPK.word_id in T1, T8, T9, T18, T19.
      apply (rd_step LB cr fx1 fx3 R2 R3 0x37118 0x372c8 M2 M3 model K sp os HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS3 MG3 FRZ3).
      intros HH3.
      assert (AG03 : forall a n, (ois <= a /\ a + n <= ois + 272) -> L5C.agree_on M M3 a n).
      { intros a n H. apply (L5C.agree_on_trans M M2 M3); [apply AG02; [lia|lia| apply NDR; lia]|]. intros i Hi; apply FRZ3; lia. }
      apply (FIN fx3 R3 M3 (de + len1) (rem - len1) g st len1).
      * exact T1.
      * intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite T2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
      * exact T10.
      * exact E264.
      * exact E272.
      * exact E280.
      * exact E288.
      * lia.
      * lia.
      * lia.
      * apply (L5C.u64_at_agree RSEGS M M3); [apply AG03; lia|lia|lia| exact I40].
      * apply (PMF.u32_at_agree RSEGS M M3); [apply AG03; lia|lia|lia| replace (ois + 152) with (ois + 120 + 32) by lia; exact J32].
      * lia.
      * exact JST.
      * intros E; exact E.
      * lia.
      * lia.
      * lia.
      * intros X. exfalso. lia.
      * apply (PMK.ek_trans L LB sp 20480 WA M M1 M3 EK01). apply (PMK.ek_trans L LB sp 20480 WA M1 M2 M3 EK12).
        apply (rd_ek LB sp os WA M2 M3 FRZ3 STK2 BR INWf).
      * apply (PMK.dk_grows L LB sp 20480 M M3). apply (mem_grows_trans M M1 M3 MG1). apply (mem_grows_trans M1 M2 M3 MG2 MG3).
      * apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2).
      * exact HH3.
    + (* [comment removed for export] *)
      assert (EL : len1 = rem) by (destruct L1c as [X|X]; [exfalso; apply NK; exact X| exact X]).
      rewrite EL in X9.
      LeanFeed.pfeed P (PMSRDP.srBne_conc fx1 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os
                   | 37%nat => p | 38%nat => k | 39%nat => rem
                   | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                   | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
      PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & T18 & E280 & E288 & E264 & E272 & S8 & S16 & S24 & S32 & S40)); PMK.pvz_clrT.
      apply (rd_step LB cr fx1 fx3 R2 R3 0x37118 0x382d4 M2 M3 model K sp os HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS3 MG3 FRZ3).
      intros HH3.
      apply (FILLC fx3 R3 M3 rem T1); try (PMK.rk; fail); try assumption.
      all: lazymatch goal with
           | |- forall x, In x _ -> _ => intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [PMK.rk|]); destruct Hx
           | |- forall i, 0 <= i < 2 ^ 64 -> _ =>
               intros i Hi N1 N2 N3; rewrite FRZ3 by (first [exact Hi | intros X; apply N1; lia | intros X; apply N2; lia]);
               rewrite FRZ2 by (first [exact Hi | intros X; apply N3; lia]); apply FRZ1; [exact Hi| intros X; apply N1; lia]
           | |- mem_grows _ _ => apply (mem_grows_trans M M1 M3 MG1); apply (mem_grows_trans M1 M2 M3 MG2 MG3)
           | _ => lia
           end.
  - (* [comment removed for export] *)
    assert (rem = 0) by lia. subst rem.
    destruct (Z.eq_dec k 16384) as [K16|K16].
    + (* [comment removed for export] *)
      subst k.
      destruct JST as [ST0|ST2].
      * (* [comment removed for export] *)
        subst st.
        destruct (D16K eq_refl) as (q0 & c0 & BIN & W1 & W2).
        assert (TIN : In (q0, c0) LB) by (unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact BIN).
        LeanFeed.pfeed P (PMSRDP.srA0d_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p
                     | 45%nat => ois | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36 | exact AL37]
                               | replace (ois + 152) with (ois + 120 + 32) by lia; assumption ]).
        PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & _ & X18 & X19 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
        apply (rd_step LB cr fx fx1 R R1 0x370d0 0x5d574 M M1 model K sp os HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS1 MG1
                 (fun i Hi N1 _ => FRZ1 i Hi N1)).
        intros HH1.
        assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (PMK.stk_grows L M M1 sp 20480 MG1 STK)).
        assert (EK1 : PMK.ek L LB sp 20480 [] M M1).
        { apply (PMFR.ek_of_piece RSEGS L KL LB sp 20480 M M1 (fun a => sp - 48 <= a < sp - 48 + 48)
                 ltac:(intros a Ha N; apply FRZ1; [exact Ha| exact N]) STK (PMFR.brange_hi L LB BR)). intros a Pa. lia. }
        assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
        assert (IA1 : PM.iss_at RSEGS AD PMSP.T3 M1 (ois) str (PM.STRM g eg 0)).
        { apply (PMFR.iss_keep RSEGS AD L KL LB sp 20480 [] M M1 EK1 STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA]. }
        assert (BASE1 : PMST.base_ok RSEGS AD M1).
        { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 [] M M1 EK1); first [exact BASE | intros a _; apply L5C.outside_nil]. }
        assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 48) 16384).
        { apply (PMK.stk_call L M1 sp 20480 (sp - 48) 16384 STK1); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
        (* [comment removed for export] *)
        assert (APG : p + 16384 <= g \/ eg <= p).
        { pose proof (PMPK.iss_unread_where RSEGS AD M (ois) str _ IA) as [(Y1 & Y2)|(c1 & n1 & q1 & -> & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in *.
          - left. destruct (BR _ _ TIN) as (_ & _ & Z4). unfold hl_ceil in Z4. lia.
          - pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). destruct VS as (_ & _ & _ & _ & _ & _ & HC1 & _).
            destruct (apart_pt p 16384 q1 c1 ltac:(lia) ltac:(lia)) as [X|X]; [| left; lia| right; lia].
            intros a Ha. destruct (DX a Ha) as (_ & _ & _ & _ & Y6). exact (Y6 c1 n1 q1 eq_refl). }
        unfold PMPSS.xsgetn_spec, PMPS.xsgetn_spec in XS. cbn [pa_xsgetn AD PnLayoutS_u.ADDR_S] in XS.
        apply (XS fx1 R1 M1 model K LB cr (sp - 48) 225876 (ois) p str (PM.STRM g eg 0) HH1 MOK K0).
        { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
          split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
        { rewrite L5K.rl10. exact X10. }
        { rewrite L5K.rl11. rewrite (KS1 11%nat) by PMK.inl. exact A11. }
        { rewrite L5K.rl12. rewrite (KS1 12%nat) by PMK.inl. exact A12. }
        { lia. } { lia. } { exact AL37. } { exact IA1. } { exact BASE1. } { exact SINC. }
        { exists q0, c0. split; [exact TIN| unfold PM.CHUNK; lia]. }
        { unfold PM.CHUNK. cbn [PM.sm_g PM.sm_eg]. exact APG. }
        cbn [PM.sm_g PM.sm_eg PM.sm_st]. unfold PM.CHUNK.
        intros fx2 R2 M2 c RP2 Y10 CEQ IA2 DD2 HP2 HH2.
        rewrite L5K.rl10 in Y10. change (PMSP.pm_scr 2) with 16384 in HP2.
        assert (CR : 0 <= c <= 16384) by (clear - CEQ SZ; Lia.lia).
        set (Wx := [(ois + 40, 8); (p, 16384)] : list L5.range).
        assert (WCx : forall a, PMK.inW Wx a -> (ois + 40 <= a < ois + 48) \/ (p <= a < p + 16384)).
        { intros a (r0 & Hin & Hr). unfold Wx in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
        assert (EKc : PMK.ek L LB (sp - 48) 16384 Wx M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
        assert (SCc : 0 <= 16384) by lia.
        assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 48) 16384 Wx STK1 HP2); lia).
        pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
        assert (HI2 : forall a n, sp - 48 <= a -> a + n <= 2 ^ 64 -> (a + n <= ois + 40 \/ ois + 48 <= a) -> L5C.agree_on M1 M2 a n).
        { intros a n H1 H2 H3. apply (PMPK.ag_hi RSEGS L KL LB (sp - 48) 16384 Wx M1 M2 EKc STKc SCc a n H1 H2). intros i Hi I. apply WCx in I.
          destruct I as [I|I]; [clear - Hi I H3; lia|]. destruct (BR _ _ TIN) as (_ & _ & Z4). clear - Hi I H1 W1 W2 Z4 SLO. unfold hl_ceil in *. lia. }
        assert (BASE2 : PMST.base_ok RSEGS AD M2).
        { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB (sp - 48) 16384 Wx M1 M2 EKc); [| | | | exact BASE1].
          all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCx in I; pose proof (DXI a) as Y;
               cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S] in Ha.
          all: destruct I as [I|I]; [clear - I Ha SLO F1 STOP; lia| apply (Y I); rewrite (ly_img_lo L LY), (ly_img_hi L LY); clear - Ha; lia]. }
        pose proof BASE2 as (IMG2 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG2.
        pose proof IA2 as (K0' & _ & _ & K16 & _ & _ & K40 & _ & _ & _ & _ & _ & KIOS & _ & KE2).
        destruct KIOS as (_ & L32 & L36 & L40 & _ & _ & LD & _ & _).
        cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios AD PnLayoutS_u.ADDR_S] in *.
        assert (R2_2 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl; exact X2).
        assert (R2_8 : getr R2 (PMK.reg 8) = Z_to_bv 64 (os)) by (rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl; exact X8).
        assert (R2_9 : getr R2 (PMK.reg 9) = Z_to_bv 64 0) by (rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl; exact X9).
        assert (R2_18 : getr R2 (PMK.reg 18) = Z_to_bv 64 16384) by (rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl; exact X18).
        assert (R2_19 : getr R2 (PMK.reg 19) = Z_to_bv 64 p) by (rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl; exact X19).
        assert (AG02 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (a + n <= ois + 40 \/ ois + 48 <= a) -> L5C.agree_on M M2 a n).
        { intros a n H1 H2 H3. apply (L5C.agree_on_trans M M1 M2); [intros i Hi; apply FRZ1; lia| apply HI2; lia]. }
        assert (C8' : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C8]).
        assert (C16' : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C16]).
        assert (C24' : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C24]).
        assert (C32' : L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C32]).
        assert (C40' : L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C40]).
        assert (F264 : L5.u64_at RSEGS M2 (os + 264) qc) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S264]).
        assert (F272 : L5.u64_at RSEGS M2 (os + 272) 16384) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S272]).
        assert (F280 : L5.u64_at RSEGS M2 (os + 280) de) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S280]).
        assert (F288 : L5.u64_at RSEGS M2 (os + 288) 0) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S288]).
        assert (F240 : L5.u64_at RSEGS M2 (os + 240) (ois)) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S240]).
        assert (F248 : L5.u64_at RSEGS M2 (os + 248) (ois + 16)) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S248]).
        assert (F256 : L5.defined M2 (os + 256) 8).
        { apply (L5C.defined_agree M M2); [apply AG02; lia|]. apply (L5.defined_sub M os 296); [exact SDEF|lia|lia]. }
        assert (WF2 : L5.writable RSEGS M2 (os + 256) 40).
        { apply (L5C.writable_of_defined RSEGS); [|lia|lia]. apply (L5C.defined_agree M M2); [apply AG02; lia|]. apply (L5.defined_sub M os 296); [exact SDEF|lia|lia]. }
        assert (EK2 : PMK.ek L LB sp 20480 WA M1 M2).
        { apply (PMK.ek_callee_in' RSEGS L KL LB LB sp 20480 (sp - 48) 16384 WA Wx M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB BR)|].
          intros a I. right. apply WCx in I. destruct I as [I|I]; [apply INWg; lia| apply INWd; lia]. }
        assert (EK01 : PMK.ek L LB sp 20480 WA M M1).
        { apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 WA [] M M1 EK1); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil. }
        destruct (Z.eq_dec c 16384) as [E16|N16].
        -- (* [comment removed for export] *)
           revert E16 Y10 CEQ CR DD2. intros -> Y10 CEQ CR DD2.
           LeanFeed.pfeed P (PMSRDP.srE1_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p
                        | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                        | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => ois | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36 | exact AL37]
                                  | replace (ois + 152) with (ois + 120 + 32) by lia; assumption
                                  | replace (ois + 156) with (ois + 120 + 36) by lia; assumption
                                  | replace (ois + 160) with (ois + 120 + 40) by lia; assumption ]).
           PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T18 & T19 & E264 & E272 & E280 & E288 & _)); PMK.pvz_clrT.
           rewrite PMPK.word_id in T1, T8, T9, T18, T19.
           apply (rd_step LB cr fx2 fx3 R2 R3 0x37254 0x372c8 M2 M3 model K sp os HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS3 MG3 FRZ3).
           intros HH3.
           apply (FIN fx3 R3 M3 de 0 (g + 16384) 0 16384).
           ++ exact T1.
           ++ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite T2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
           ++ rewrite (KS3 10%nat) by PMK.inl. exact Y10.
           ++ exact E264.
           ++ exact E272.
           ++ exact E280.
           ++ exact E288.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ apply (L5C.u64_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact K40].
           ++ apply (PMF.u32_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| replace (ois + 152) with (ois + 120 + 32) by lia; exact L32].
           ++ clear - CEQ SZ. Lia.lia.
           ++ left. reflexivity.
           ++ intros E; discriminate E.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ intros X. exfalso. lia.
           ++ apply (PMK.ek_trans L LB sp 20480 WA M M1 M3 EK01). apply (PMK.ek_trans L LB sp 20480 WA M1 M2 M3 EK2).
              apply (rd_ek LB sp os WA M2 M3 FRZ3 STK2 BR INWf).
           ++ apply (PMK.dk_trans L LB sp 20480 M M1 M3); [apply (PMK.dk_grows L LB sp 20480 M M1 MG1)|].
              apply (PMK.dk_trans L LB sp 20480 M1 M2 M3); [|apply (PMK.dk_grows L LB sp 20480 M2 M3 MG3)].
              apply (PMK.dk_callee L LB LB sp 20480 (sp - 48) 16384 Wx M1 M2 HP2 (incl_refl _)); lia.
           ++ apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2).
           ++ exact HH3.
        -- (* [comment removed for export] *)
           LeanFeed.pfeed P (PMSRDP.srE2_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p
                        | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                        | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => ois | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36 | exact AL37]
                                  | replace (ois + 152) with (ois + 120 + 32) by lia; assumption
                                  | replace (ois + 156) with (ois + 120 + 36) by lia; assumption
                                  | replace (ois + 160) with (ois + 120 + 40) by lia; assumption
                                  | apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 (ois + 120) 152); [exact LD|lia|lia]|lia|lia] ]).
           PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & E152 & E264 & E272 & E280 & E288 & _)); PMK.pvz_clrT.
           rewrite PMPK.word_id in T1, T8, T9, T18, T19.
           set (P3 := fun a => (sp - 48 <= a < sp - 48 + 48) \/ (os + 256 <= a < os + 256 + 40) \/ (ois + 152 <= a < ois + 152 + 4)).
           assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
           { intros a Ha N. apply FRZ3; [exact Ha| | |]; intros X; apply N; unfold P3; [left| right; left| right; right]; exact X. }
           apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model fx2 fx3 R2 0x37254 R3 0x372c8 M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 FRZ3').
           { intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P3 in Pa. lia. }
           { intros a. apply PMK.or_dec; [apply PMK.rng_dec| apply PMK.or_dec; apply PMK.rng_dec]. }
           intros HH3.
           apply (FIN fx3 R3 M3 de 0 (g + c) 2 c).
           ++ exact T1.
           ++ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite T2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
           ++ rewrite (KS3 10%nat) by PMK.inl. exact Y10.
           ++ exact E264.
           ++ exact E272.
           ++ exact E280.
           ++ exact E288.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ apply (L5C.u64_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact K40].
           ++ exact E152.
           ++ clear - CEQ SZ. Lia.lia.
           ++ right. reflexivity.
           ++ intros _. reflexivity.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ intros _. split; reflexivity.
           ++ apply (PMK.ek_trans L LB sp 20480 WA M M1 M3 EK01). apply (PMK.ek_trans L LB sp 20480 WA M1 M2 M3 EK2).
              apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 WA M2 M3 P3 FRZ3' STK2 (PMFR.brange_hi L LB BR)).
              intros a [Pa|[Pa|Pa]]; [left; lia| right; apply INWf; lia| right; apply INWs; lia].
           ++ apply (PMK.dk_trans L LB sp 20480 M M1 M3); [apply (PMK.dk_grows L LB sp 20480 M M1 MG1)|].
              apply (PMK.dk_trans L LB sp 20480 M1 M2 M3); [|apply (PMK.dk_grows L LB sp 20480 M2 M3 MG3)].
              apply (PMK.dk_callee L LB LB sp 20480 (sp - 48) 16384 Wx M1 M2 HP2 (incl_refl _)); lia.
           ++ apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2).
           ++ exact HH3.
      * (* [comment removed for export] *)
        subst st.
        LeanFeed.pfeed P (PMSRDP.srA0e_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p
                     | 45%nat => ois | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36 | exact AL37]
                               | replace (ois + 152) with (ois + 120 + 32) by lia; assumption ]).
        PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X10 & X11 & C288 & C40 & C32 & C24 & C16 & C8 & C264 & C272 & C280 & _)); PMK.pvz_clrT.
        apply (rd_step LB cr fx fx1 R R1 0x370d0 0x372c8 M M1 model K sp os HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS1 MG1 FRZ1).
        intros HH1.
        apply (FIN fx1 R1 M1 de 0 g 2 0).
        -- rewrite (KS1 1%nat) by PMK.inl. reflexivity.
        -- intros x Hx. apply KS1. revert x Hx. apply (PMPK.sub_in PMSRDP.KS_srA0e). vm_compute. reflexivity.
        -- exact X10.
        -- exact C264.
        -- exact C272.
        -- exact C280.
        -- exact C288.
        -- lia.
        -- lia.
        -- lia.
        -- apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FRZ1; lia|lia|lia| exact I40].
        -- apply (PMF.u32_at_agree RSEGS M M1); [intros i Hi; apply FRZ1; lia|lia|lia| replace (ois + 152) with (ois + 120 + 32) by lia; exact J32].
        -- lia.
        -- right. reflexivity.
        -- intros E; exact E.
        -- lia.
        -- lia.
        -- lia.
        -- intros _. split; reflexivity.
        -- apply (rd_ek LB sp os WA M M1 FRZ1 STK BR INWf).
        -- apply (PMK.dk_grows L LB sp 20480 M M1 MG1).
        -- apply (PMK.stk_grows L M M1 sp 20480 MG1 STK).
        -- exact HH1.
    + (* [comment removed for export] *)
      LeanFeed.pfeed P (PMSRDP.srA0f_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
      PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X11 & X12 & X18 & X19 & C280 & C40 & C32 & C24 & C16 & C8 & C264 & C272 & C288 & _)); PMK.pvz_clrT.
      apply (rd_step LB cr fx fx1 R R1 0x370d0 0x382d4 M M1 model K sp os HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS1 MG1 FRZ1).
      intros HH1.
      apply (FILLC fx1 R1 M1 0 X1 X2 X8 X9); try assumption.
      all: lazymatch goal with
           | |- getr _ (PMK.reg 10) = _ => rewrite (KS1 10%nat) by PMK.inl; exact A10
           | |- getr _ (PMK.reg 18) = _ => rewrite Z.sub_0_r; exact X18
           | |- forall x, In x _ -> _ => intros x Hx; apply KS1; revert x Hx; apply (PMPK.sub_in PMSRDP.KS_srA0f); vm_compute; reflexivity
           | |- forall i, 0 <= i < 2 ^ 64 -> _ => intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]
           | _ => lia
           end.
Qed.

End WithHeap.
End PGSRD.
