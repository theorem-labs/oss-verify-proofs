(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseSomeAt_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallAt_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SPT.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Definition NF : nat := 52.

Lemma last_cases : forall (l : list Z), l = [] \/ exists l' y, l = l' ++ [y].
Proof. intros l. destruct l as [|a l0]; [left; reflexivity|]. right. destruct (@exists_last _ (a :: l0) ltac:(discriminate)) as (l' & y & H). exists l', y. exact H. Qed.
Lemma app_last_inj : forall (l1 l2 : list Z) x y, l1 ++ [x] = l2 ++ [y] -> x = y.
Proof. intros l1 l2 x y H. apply app_inj_tail in H. exact (proj2 H). Qed.
Lemma win_le : forall (M : mem) P ps, PML.parser_at M P ps -> match PML.ps_win ps with Some (p, e) => p <= e | None => True end.
Proof.
  intros M P ps H. unfold PML.parser_at in H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw & _).
  destruct (PML.ps_win ps) as [[p e]|]; [exact (proj2 (proj2 Hw)) | exact I].
Qed.
Lemma pa_def : forall (M1 : mem) P1 ps1, PML.parser_at M1 P1 ps1 -> L5.defined M1 P1 272.
Proof. intros M1 P1 ps1 H. unfold PML.parser_at in H. repeat (destruct H as [_ H]). exact H. Qed.
Lemma pa_stack : forall (M1 : mem) P1 ps1, PML.parser_at M1 P1 ps1 -> L5.bytes_at RSEGS M1 (PML.ps_sb ps1) (PML.ps_stack ps1).
Proof.
  intros M1 P1 ps1 H. unfold PML.parser_at in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _). exact Hb.
Qed.

Lemma win_ok_tr : forall (M M' : mem) LBo ps ps', PML.ps_win ps' = PML.ps_win ps -> PML.win_ok M LBo ps ->
  (forall ch p n, In (ch, 16384) LBo -> ch <= p -> p + n <= ch + 16384 -> L5.defined M p n -> L5.defined M' p n) -> PML.win_ok M' LBo ps'.
Proof.
  intros M M' LBo ps ps' Hw HW HD. unfold PML.win_ok in *. rewrite Hw. destruct (PML.ps_win ps) as [[p e]|]; [|exact I].
  destruct HW as (ch & Hch & C1 & C2 & Hwd). exists ch. split; [exact Hch|]. split; [exact C1|]. split; [exact C2|]. apply (HD ch p (e - p) Hch C1 ltac:(lia) Hwd).
Qed.
Lemma buf_bound_tr : forall ps ps' B, PML.ps_win ps' = PML.ps_win ps -> Z.of_nat (length (PML.ps_buf ps')) = Z.of_nat (length (PML.ps_buf ps)) -> PML.buf_need ps' <= PML.buf_need ps ->
  PML.buf_bound ps B -> PML.buf_bound ps' B.
Proof. intros ps ps' B Hw Hl Hn (H1 & H2). unfold PML.buf_bound, PML.winlen in *. rewrite Hw, Hl. split; [lia | exact H2]. Qed.
Lemma buf_bound_of_stale : forall ps ps' B, PML.ps_win ps' = PML.ps_win ps -> Z.of_nat (length (PML.ps_buf ps')) = Z.of_nat (length (PML.ps_buf ps)) -> PML.buf_need ps' = 0 ->
  PMS.buf_bound_stale ps B -> PML.buf_bound ps' B.
Proof. intros ps ps' B Hw Hl Hn (H1 & H2 & H3). unfold PML.buf_bound, PML.winlen in *. rewrite Hw, Hl, Hn. split; [lia | exact H2]. Qed.
Lemma bytes_prefix : forall (M : mem) p (s1 s2 : list Z), L5.bytes_at RSEGS M p (s1 ++ s2) -> L5.bytes_at RSEGS M p s1.
Proof. intros M p s1 s2 H i Hi. specialize (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 in H by exact Hi. exact H. Qed.

Definition X0w (wptrx stx morex : expr) : PSK.pexprs :=
  PSK.PX (EVar 41) wptrx stx (EVar 43) (EVar 44) morex (EVar 46) (EVar 35) (EVar 36) (EVar 37) (EVar 38) (EVar 39) (EVar 40) (EVar 47) (EVar 48) (ELit 0).
Definition X0 (stx morex : expr) : PSK.pexprs := X0w (EVar 32) stx morex.

Definition noeb : nat -> list (bv 8) := fun _ => [].
Definition PE : expr := EVar 37.  Definition CE : expr := APC.escale 2 (EVar 35).
Definition BL0 : CA.blocks := [(PE, CE); (EVar 38, EVar 40)].

Section Pt.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variables (mw : option (Z * Z)) (LBo : list (Z * Z)) (cr : credit) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate).
Variables (R : bvmap 5 word) (M : mem) (model : Model).
Variables (SCRC : Z) (HDECL : CH.hdecl) (Pb Vb Eb : expr) (line0 pos0 : Z) (xv : list Z) (ebf : nat -> list (bv 8)).

Let wptr := fst (PSA.wincells mw).
Let wend := snd (PSA.wincells mw).
Let bcap := PML.ps_bcap ps.
Let k0 := bcap / 2.
Let bptr := PML.ps_bptr ps.
Let size0 := Z.of_nat (length (PML.ps_buf ps)).
Let sb := PML.ps_sb ps.
Let scap := PML.ps_scap ps.
Let slen := Z.of_nat (length (PML.ps_stack ps)).
Let level := PML.ps_level ps.
Let done := PML.b2z (PML.ps_done ps).
Let more := PML.b2z (PML.ps_more ps).
Let SCR := CH.hd_scr HDECL.

Definition E0 : env :=
  Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) ([wptr; wend; B; k0; size0; bptr; sb; slen; scap; level; PML.ps_st ps; PML.ps_sst ps; PML.ps_nst ps; more; done; line0; pos0] ++ xv) 0)))
      ebf.

Definition inst : Prop :=
  heap_iface_ok L SCFG HI /\ PmLayout.pm0_layout L /\
  hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model) /\
  PML.entry L R M sp r SCRC /\ 0 <= SCR <= SCRC /\ SCRC <= 2 ^ 20 /\
  PML.parser_at M P (PML.ps_set_win ps mw) /\ PML.wf_ps_stale ps /\ 0 <= level <= 1025 /\ size0 < 2 ^ 26 /\ 0 <= PML.ps_st ps <= 255 /\
  PML.vis_at M V /\ PML.ec_at M E 0 /\ PML.ls_ok g M /\ PML.pcredit_x L cr ps kx bx /\
  PML.obj_on_stack L sp P 272 /\ PML.obj_on_stack L sp V 48 /\ PML.obj_on_stack L sp E 16 /\ PML.apart P 272 V 48 /\ PML.apart P 272 E 16 /\ PML.apart V 48 E 16 /\
  PML.u64 M (P + 160) line0 /\ PML.u64 M (P + 168) pos0 /\ 0 <= line0 < 2 ^ 64 /\ 0 <= pos0 < 2 ^ 64 /\

  uv E0 Pb = P /\ uv E0 Vb = V /\ uv E0 Eb = E /\
  APC.expr_vars_lt NF Pb = true /\ APC.expr_vars_lt NF Vb = true /\ APC.expr_vars_lt NF Eb = true.
Hypothesis INST : inst.

Lemma SPF : sp mod 16 = 0 /\ 0x7fff7f800000 + SCRC <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\ L5.defined M (sp - SCRC) SCRC /\ hl_ceil L + SCRC <= sp /\ 0 <= SCR <= SCRC.
Proof.
  destruct INST as (_ & _ & _ & Hentry & HS1 & _). destruct Hentry as (_ & _ & _ & _ & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as F. destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  repeat split; try lia; try assumption.
Qed.

Lemma NUM :
  block_range L bptr bcap /\ block_range L sb scap /\ L5.defined M bptr bcap /\ L5.defined M sb scap /\ (bptr + bcap <= sb \/ sb + scap <= bptr) /\
  bcap = 2 * k0 /\ 264 <= bcap <= 2 ^ 27 /\ size0 < bcap /\ 1 <= slen <= 1027 /\ slen <= scap /\ 66 <= scap <= 1056 /\
  0 <= PML.ps_sst ps <= 11 /\ 0 <= PML.ps_nst ps <= 7 /\ 0 <= done <= 1 /\ 0 <= more <= 1.
Proof.
  destruct INST as (HIok & LAY & HH & _ & _ & _ & HPA & HWF & _ & _ & _ & _ & _ & _ & HPC & _).
  pose proof HPA as H. unfold PML.parser_at in H. cbn [PML.ps_set_win PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_sb PML.ps_scap PML.ps_stack PML.ps_st] in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstr & Hb264 & _ & _ & _ & _ & Hsl & _).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  assert (I1 : In (bptr, bcap) (PML.ps_blocks ps ++ LBo)) by (left; reflexivity).
  assert (I2 : In (sb, scap) (PML.ps_blocks ps ++ LBo)) by (right; left; reflexivity).
  destruct (Hwf _ I1) as (BR1 & BD1 & BA1). destruct (Hwf _ I2) as (BR2 & BD2 & BA2). cbn [fst snd] in *.
  unfold PML.ps_blocks in Hnd. fold bptr bcap sb scap in Hnd. cbn [map fst app] in Hnd. inversion Hnd as [|x l N1 N2]; subst.
  assert (Nsb : sb <> bptr) by (intros X; apply N1; apply list_elem_of_In; left; exact X).
  pose proof (L5C.blocks_apart_in _ _ _ sb scap BA1 (L5C.in_lb_remove_neq bptr sb scap _ I2 Nsb)) as A1.
  destruct Hstr as (_ & Hc8 & Hlt). fold bcap size0 in Hc8, Hlt.
  assert (Hk : bcap = 2 * k0).
  { unfold k0. pose proof (Z.div_mod bcap 8 ltac:(lia)) as D. rewrite Hc8 in D. rewrite D at 2. replace (8 * (bcap / 8) + 0) with ((4 * (bcap / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
  destruct HWF as (Wn & n' & W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)). cbn [PML.ps_set_nst PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level] in *.
  destruct HPC as (_ & _ & (HP27 & _)).
  assert (Hs1 : 1 <= slen) by (unfold slen; rewrite W5; cbn [length]; lia).
  assert (Hsc : 66 <= scap <= 1056) by (fold scap in W4; cbn [In] in W4; lia).
  fold bcap in HP27.
  split; [exact BR1|]. split; [exact BR2|]. split; [exact BD1|]. split; [exact BD2|]. split; [exact A1|]. split; [exact Hk|].
  assert (Hm : 0 <= more <= 1) by (unfold more, PML.b2z; case (PML.ps_more ps); lia).
  assert (Hd : 0 <= done <= 1) by (unfold done, PML.b2z; case (PML.ps_done ps); lia).
  repeat split; try assumption; try lia; try (unfold slen; lia).
Qed.

Lemma EV0 : forall x : reg, ev E0 (ridx x) = getr R x.
Proof. intros x. apply CL5.ev_reg. Qed.
Lemma UU : uv E0 (EVar 2) = sp /\ uv E0 Pb = P /\ uv E0 Eb = E /\ uv E0 Vb = V.
Proof.
  destruct INST as (_ & _ & _ & Hentry & HS1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UP & UV & UE & _).
  destruct Hentry as (_ & _ & Hsp & _). pose proof SPF as (S1 & S2 & S3 & S4 & _ & _ & S7).
  split; [unfold PB.uv; cbn [edenot]; rewrite (EV0 2%bv), Hsp; apply u64_of_Z; lia|]. split; [exact UP|]. split; [exact UE | exact UV].
Qed.
Lemma U2 : bv_unsigned (ev E0 2) = sp.
Proof. exact (proj1 UU). Qed.
Lemma TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Proof. destruct INST as (_ & LAY & _ & Hentry & _). destruct Hentry as (_ & _ & _ & Htp & _). rewrite (EV0 4%bv), Htp, (PmLayout.ly_tp L LAY). reflexivity. Qed.

Lemma kn_okw : forall (C : PSK.consts) wptrx wendx stx morex,
  PSK.c_vt_parser C = PML.VT_PARSER -> PSK.c_vt_func C = PML.VT_FUNC -> PSK.c_vt_visitor C = PML.VT_VISITOR ->
  PSK.c_hull_lo C = 0x10000 /\ PSK.c_hull_hi C = 0xf8000 -> PSK.c_img_lo C = 0x10000 /\ PSK.c_img_hi C = PML.IMG_RO_HI -> PSK.c_scr C = SCR ->
  uv E0 stx = PML.ps_st ps -> uv E0 morex = more -> edenot E0 wptrx = Z_to_bv 64 wptr -> edenot E0 wendx = Z_to_bv 64 wend ->
  know_ok RSEGS E0 M (SPK.kn C false Pb Vb Eb (EVar 2) wendx (X0w wptrx stx morex)).
Proof.
  intros C wptrx wendx stx morex C1 C2 C3 C4 C5 C6 Lst Lmore Lwp Lwe.
  pose proof UU as (U2' & UP & UE & UV). pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof NUM as (BR1 & BR2 & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  destruct INST as (HIok & LAY & HH & Hentry & HS1 & HS2 & HPA & HWF & HLV & HSZ & N10 & HVIS & HEC & HLS & HPC & OP & OV & OE & AP1 & AP2 & AP3 & Hline0 & Hpos0 & Q1 & Q2 & _).
  destruct OP as (OP1 & OP2 & OP3), OV as (OV1 & OV2 & _), OE as (OE1 & OE2 & _). fold SCR in HS1.
  assert (DSCR : L5.defined M (sp - SCR) SCR) by (eapply (L5.defined_sub _ _ _ _ _ S5); lia).
  unfold SPK.kn, know_ok. rewrite Forall_app. split.
  - eapply (SPA.kn_sem_ok C C1 C2 C4 ltac:(rewrite C6; lia) Pb Vb Eb (EVar 2) wendx (X0w wptrx stx morex) E0 M P E V sp (PML.ps_set_win ps mw) line0 pos0 0
             UP UE UV U2') with (L := L); rewrite ?C6;
      cbn [PSK.x_level PSK.x_wptr PSK.x_st PSK.x_sst PSK.x_nst PSK.x_more PSK.x_done PSK.x_k PSK.x_size PSK.x_p PSK.x_sb PSK.x_slen PSK.x_scap PSK.x_line PSK.x_pos PSK.x_ec X0w];
      cbn [PML.ps_set_win PML.ps_level PML.ps_win PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_bcap PML.ps_buf PML.ps_bptr PML.ps_sb PML.ps_stack PML.ps_scap];
      fold bcap bptr size0 sb scap slen level.
    all: try (split; lia). all: try lia.
    all: try exact HPA. all: try exact Hline0. all: try exact Hpos0. all: try exact LAY. all: try (destruct HEC as (X & _); exact X).
    all: try exact Lst. all: try exact Lmore. all: try exact Lwp. all: try exact Lwe.
    all: try reflexivity.
    all: try (unfold PB.uv; cbn [edenot]; apply u64_of_Z; first [lia | unfold level, done, size0, slen in *; lia]).
    + unfold PB.uv. cbn [edenot]. change (ev E0 35) with (Z_to_bv 64 k0). rewrite u64_of_Z by lia. lia.
    + destruct BR1 as (B0 & B1 & B2 & B3 & B4). unfold PB.uv. cbn [edenot]. change (ev E0 37) with (Z_to_bv 64 bptr). apply u64_of_Z. unfold hl_ceil in B4. lia.
    + destruct BR2 as (B0 & B1 & B2 & B3 & B4). unfold PB.uv. cbn [edenot]. change (ev E0 38) with (Z_to_bv 64 sb). apply u64_of_Z. unfold hl_ceil in B4. lia.
    + split; assumption.
    + split; assumption.
  - destruct HLS as (IMGRO & _). destruct HEC as (_ & HEdef & _). unfold PML.apart in AP1, AP2, AP3.
    pose proof (pa_def _ _ _ HPA) as HdefP.
    apply (SPA.kn_frz_ok C C3 C5 ltac:(rewrite C6; lia) Pb Vb Eb (EVar 2) E0 M P E V sp UP UE UV U2'); rewrite ?C6; try assumption; try (split; lia); try lia.
Qed.
Lemma kn_ok : forall (C : PSK.consts) stx morex,
  PSK.c_vt_parser C = PML.VT_PARSER -> PSK.c_vt_func C = PML.VT_FUNC -> PSK.c_vt_visitor C = PML.VT_VISITOR ->
  PSK.c_hull_lo C = 0x10000 /\ PSK.c_hull_hi C = 0xf8000 -> PSK.c_img_lo C = 0x10000 /\ PSK.c_img_hi C = PML.IMG_RO_HI -> PSK.c_scr C = SCR ->
  uv E0 stx = PML.ps_st ps -> uv E0 morex = more ->
  know_ok RSEGS E0 M (SPK.kn C false Pb Vb Eb (EVar 2) (EVar 33) (X0 stx morex)).
Proof. intros C stx morex C1 C2 C3 C4 C5 C6 Lst Lmore. exact (kn_okw C (EVar 32) (EVar 33) stx morex C1 C2 C3 C4 C5 C6 Lst Lmore eq_refl eq_refl). Qed.

Definition W : list L5.range := PMS.W_parc P V E.
Lemma STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct INST as (_ & _ & _ & _ & HS1 & _). fold SCR. repeat split; lia. Qed.
Lemma SCRP : 0 <= CH.hd_scr HDECL.
Proof. destruct INST as (_ & _ & _ & _ & HS1 & _). exact (proj1 HS1). Qed.
Lemma STATW : forall a, 0xd4df8 <= a < 0xd4dfa \/ 0xf6848 <= a < 0xf6848 + 544 -> CH2.wclient L sp a.
Proof.
  destruct INST as (_ & LAY & _).
  intros a Ha. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7). split; [lia|]. right. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY). split; [lia|].
  split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia|].
  split; [intros X; destruct (PmLayout.ly_ro_img L LAY a X ltac:(rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia)) as [Q|[Q|Q]]; lia|].
  unfold in_errno. rewrite (PmLayout.ly_errno L LAY). lia.
Qed.
Lemma W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a.
Proof.
  pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  destruct INST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OP & OV & OE & _). destruct OP as (OP1 & OP2 & _), OV as (OV1 & OV2 & _), OE as (OE1 & OE2 & _).
  intros w a Hw Hin. unfold W, PMS.W_parc, PML.W_par in Hw. cbn [app] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
  - split; [lia | left; lia].
  - split; [lia | left; lia].
  - apply STATW. lia.
  - apply STATW. lia.
  - split; [lia | left; lia].
Qed.

Lemma CRS_OK : forall seg wlen, (wlen = 0 \/ exists ch, In (ch, 16384) LBo /\ ch <= seg /\ seg + wlen <= ch + 16384) -> 0 <= wlen -> 0 <= seg -> seg + wlen < 2 ^ 64 ->
  nth 1 xv 0 = seg -> nth 2 xv 0 = wlen ->
  forall rg : SGP.region, In rg [(Vb, 0, ELit 48); (EVar 50, 0, EVar 51)] -> SGP.region_vars_lt NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a).
Proof.
  intros seg wlen Hch Hw0 Hs0 Hs1 X1 X2.
  pose proof UU as (_ & _ & _ & UV). pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  destruct INST as (HIok & _ & HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OV & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FV & _). destruct OV as (OV1 & OV2 & _).
  intros rg [<-|[<-|[]]].
  - split; [unfold SGP.region_vars_lt; cbn [fst snd]; rewrite FV; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off] in Ha. fold (uv E0 Vb) in Ha. rewrite UV in Ha.
    cbn [edenot] in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia].
  - split; [reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    assert (E50 : ev E0 50 = Z_to_bv 64 seg) by (unfold E0; cbn [ev reg_ev]; rewrite <- X1; reflexivity).
    assert (E51 : ev E0 51 = Z_to_bv 64 wlen) by (unfold E0; cbn [ev reg_ev]; rewrite <- X2; reflexivity).
    rewrite E50, E51 in Ha. rewrite !u64_of_Z in Ha by lia. destruct Hch as [->|(ch & Hin & C1 & C2)]; [lia|].
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _). destruct (Hwf (ch, 16384) ltac:(right; right; exact Hin)) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in *.
    split; [lia|]. right. right. exists (ch, 16384). split; [exact Hin | cbn [fst snd]; lia].
Qed.
Lemma WRS_OK : forall rg : SGP.region, In rg [(Pb, 0, ELit 272); (Eb, 0, ELit 16)] -> SGP.region_vars_lt NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a).
Proof.
  pose proof UU as (_ & UP & UE & _).
  destruct INST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FP & _ & FE).
  intros rg [<-|[<-|[]]]; (split; [unfold SGP.region_vars_lt; cbn [fst snd]; rewrite ?FP, ?FE; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off] in Ha.
  - fold (uv E0 Pb) in Ha. rewrite UP in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by lia. exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
  - fold (uv E0 Eb) in Ha. rewrite UE in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by lia. exists (E, 16). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
Qed.
Lemma IMG_OK : forall (rg : Z * Z) (a : Z), In rg [(0x10000, PML.IMG_RO_HI)] -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Proof.
  destruct INST as (_ & LAY & _).
  intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. unfold PML.IMG_RO_HI in Ha. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY). split; [lia|].
  split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia].
Qed.
Lemma DEF0 : L5.defined M (sp - CH.hd_scr HDECL) (CH.hd_scr HDECL).
Proof. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct INST as (_ & _ & _ & _ & HS1 & _). fold SCR in HS1 |- *. eapply (L5.defined_sub _ _ _ _ _ S5); lia. Qed.
Lemma DEFC : L5.defined M (sp - SCRC) SCRC.
Proof. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7). exact S5. Qed.

Lemma FRZ : forall E', env_agree NF E0 E' ->
  uv E' (EVar 2) = sp /\ uv E' Pb = P /\ uv E' Eb = E /\ uv E' Vb = V /\ uv E' (EVar 41) = level /\ uv E' (EVar 42) = PML.ps_st ps /\ uv E' (EVar 43) = PML.ps_sst ps /\ uv E' (EVar 44) = PML.ps_nst ps /\
  uv E' (EVar 45) = more /\ uv E' (EVar 46) = done /\
  uv E' (EVar 36) = size0 /\ uv E' (EVar 38) = sb /\ uv E' (EVar 39) = slen /\ uv E' (EVar 40) = scap /\ uv E' (APC.eadd (EVar 38) (EVar 39)) = sb + slen /\ uv E' (APC.eadd (EVar 38) (EVar 40)) = sb + scap /\
  uv E' PE = bptr /\ uv E' CE = bcap /\ edenot E' (EVar 32) = Z_to_bv 64 wptr /\ edenot E' (EVar 33) = Z_to_bv 64 wend /\ uv E' (EVar 34) = B mod 2 ^ 64.
Proof.
  intros E' Hag. pose proof UU as (U2' & UP & UE & UV).
  pose proof NUM as ((B0 & B1 & B2 & B3 & B4) & (C0 & C1 & C2 & C3 & C4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). unfold hl_ceil in *.
  pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  destruct INST as (_ & _ & _ & _ & _ & _ & _ & _ & HLV & HSZ & N10 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FP & FV & FE). fold level size0 in HLV, HSZ.
  assert (A : forall x, APC.expr_vars_lt NF x = true -> uv E' x = uv E0 x) by (intros x Hx; exact (PB.uv_agree NF E0 E' x Hag Hx)).
  assert (G : forall v z, (32 <= v < NF)%nat -> ev E0 v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> uv E' (EVar v) = z).
  { intros v z Hv Hev Hz. rewrite A by (cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; lia). unfold PB.uv. cbn [edenot]. rewrite Hev. apply u64_of_Z. exact Hz. }
  assert (G38 : uv E' (EVar 38) = sb) by (apply G; [unfold NF; lia | reflexivity | lia]).
  assert (G39 : uv E' (EVar 39) = slen) by (apply G; [unfold NF; lia | reflexivity | lia]).
  assert (G40 : uv E' (EVar 40) = scap) by (apply G; [unfold NF; lia | reflexivity | lia]).
  split; [rewrite A by reflexivity; exact U2'|]. split; [rewrite A by exact FP; exact UP|]. split; [rewrite A by exact FE; exact UE|]. split; [rewrite A by exact FV; exact UV|].
  split; [apply G; [unfold NF; lia | reflexivity | lia]|]. split; [apply G; [unfold NF; lia | reflexivity | lia]|]. split; [apply G; [unfold NF; lia | reflexivity | lia]|].
  split; [apply G; [unfold NF; lia | reflexivity | lia]|]. split; [apply G; [unfold NF; lia | reflexivity | lia]|]. split; [apply G; [unfold NF; lia | reflexivity | lia]|].
  split; [apply G; [unfold NF; lia | reflexivity | unfold size0 in *; lia]|].
  split; [exact G38|]. split; [exact G39|]. split; [exact G40|].
  split; [rewrite PB.uv_eadd, G38, G39; apply Z.mod_small; lia|]. split; [rewrite PB.uv_eadd, G38, G40; apply Z.mod_small; lia|].
  split; [apply G; [unfold NF; lia | reflexivity | lia]|].
  split; [unfold CE; rewrite PB.uv_escale; rewrite (G 35%nat k0 ltac:(unfold NF; lia) eq_refl ltac:(lia)); rewrite Z.mod_small by lia; lia|].
  destruct Hag as [Hev _]. cbn [edenot]. split; [rewrite <- (Hev 32%nat) by (unfold NF; lia); reflexivity|]. split; [rewrite <- (Hev 33%nat) by (unfold NF; lia); reflexivity|].
  unfold PB.uv. cbn [edenot]. rewrite <- (Hev 34%nat) by (unfold NF; lia). change (ev E0 34) with (Z_to_bv 64 B). rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma den_BL0 : forall E', env_agree NF E0 E' -> CH2.den E' BL0 = PML.ps_blocks ps.
Proof.
  intros E' Hag. destruct (FRZ E' Hag) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H38 & _ & H40 & _ & _ & HPE & HCE & _).
  unfold CH2.den, BL0, PML.ps_blocks. cbn [map fst snd]. fold (uv E' PE) (uv E' CE) (uv E' (EVar 38)) (uv E' (EVar 40)). rewrite HPE, HCE, H38, H40. reflexivity.
Qed.

Lemma amb_def : forall NFx BLS Cred i E1 (M1 : mem) model1 a n, CH2.heap_amb L HI NFx E0 M model LBo sp HDECL W BLS Cred i E1 M1 model1 -> L5.defined M a n ->
  (sp <= a /\ a + n <= 2 ^ 47) \/ (exists ch, In (ch, 16384) LBo /\ ch <= a /\ a + n <= ch + 16384) -> L5.defined M1 a n.
Proof.
  intros NFx BLS Cred i E1 M1 model1 a n (_ & _ & _ & (cr1 & HH1 & _) & _ & Hdf) Hd Hc q Hq. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  destruct INST as (HIok & LAY & HH & _).
  destruct Hc as [[C1 C2]|(ch & Hch & C1 & C2)].
  - apply Hdf; [lia | | apply Hd; exact Hq]. split; [right; left; unfold hl_ceil; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia].
  - destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _).
    destruct (Hwf (ch, 16384) ltac:(right; right; exact Hch)) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in *.
    apply Hdf; [unfold hl_ceil in B4; lia | | apply Hd; exact Hq].
    split; [left; exists (ch, 16384); split; [exact Hch | cbn [fst snd]; lia] | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1; lia].
Qed.

Lemma below_frame : forall (F : list SGP.region) E' (M1 M' : mem), SP.F_sub F [(EVar 2, - SCR, ELit SCR); (Pb, 0, ELit 272)] = true -> env_agree NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M1 a) -> forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros F E' M1 M' HF Hag HFR a Ha. apply HFR. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0.
  pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof UU as (U2' & UP & _ & _).
  destruct INST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FP & _). destruct OP as (OP1 & OP2 & _).
  unfold hl_ceil in *. rewrite L5.unsigned_lit by lia. left.
  destruct Hin0 as [X|[X|[]]]; injection X as <- <- <-.
  - rewrite (PB.estart_agree NF E0 E' (EVar 2) (- SCR) Hag eq_refl). unfold estart. cbn [a_base a_off]. fold (uv E0 (EVar 2)). rewrite U2'. lia.
  - rewrite (PB.estart_agree NF E0 E' Pb 0 Hag FP). unfold estart. cbn [a_base a_off]. fold (uv E0 Pb). rewrite UP. lia.
Qed.

Lemma bytes_below : forall (M1 M' : mem) b n (bs : list Z), (forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> 0 <= b -> b + n <= hl_ceil L -> Z.of_nat (length bs) <= n ->
  L5.bytes_at RSEGS M1 b bs -> L5.bytes_at RSEGS M' b bs.
Proof.
  intros M1 M' b n bs HB Hb0 Hbn Hlen X. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  assert (FR : L5.frame_but [(hl_ceil L, 2 ^ 64 - hl_ceil L)] M1 M').
  { intros x Hout. rewrite <- (Z_to_bv_bv_unsigned _ x). pose proof (bv_unsigned_in_range _ x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. apply HB.
    split; [lia|]. destruct (Z_lt_dec (bv_unsigned x) (hl_ceil L)) as [Y|Y]; [exact Y|]. exfalso. apply (Hout (hl_ceil L, 2 ^ 64 - hl_ceil L) ltac:(left; reflexivity)). unfold L5.in_rng. cbn [fst snd]. lia. }
  apply (PB2.bytes_fr _ M1 M' FR); [|exact X].
  split; [lia|]. split; [unfold hl_ceil in *; lia|]. intros j Hj w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
Qed.

Lemma lsfoot_kept : forall LBk spc scr (Wc : list L5.range) a, PB2.ls_foot a -> (forall w, In w Wc -> ~ L5.in_rng w a) -> L5C.kept L LBk spc scr Wc a.
Proof.
  destruct INST as (_ & LAY & _).
  intros LBk spc scr Wc a Ha Hout. unfold PB2.ls_foot, PML.IMG_RO_HI in Ha. split; [lia|].
  split; [right; right; rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); split; [lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia]|].
  split; [unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia | exact Hout].
Qed.

Lemma ls_below : forall (M1 M' : mem) g1, g1 <> PML.LS0 -> (forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> PML.ls_ok g1 M1 -> PML.ls_ok g1 M'.
Proof.
  intros M1 M' g1 Hg HB H. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7). apply (PB2.ls_ok_keep M1 M'); [|exact Hg | exact H].
  intros a Ha. apply HB. unfold PB2.ls_foot, PML.IMG_RO_HI in Ha. unfold hl_ceil. lia.
Qed.

Lemma FRZx : forall E' k z, env_agree NF E0 E' -> (49 + k < NF)%nat -> nth k xv 0 = z -> 0 <= z < 2 ^ 64 -> uv E' (EVar (49 + k)) = z /\ eb E' = ebf.
Proof.
  intros E' k z Hag Hk Hn Hz. split; [|destruct Hag as [_ Heb]; rewrite <- Heb; reflexivity].
  rewrite (PB.uv_agree NF E0 E' (EVar (49 + k)) Hag ltac:(cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; exact Hk)). unfold PB.uv. cbn [edenot].
  assert (Hev : ev E0 (49 + k) = Z_to_bv 64 z).
  { unfold E0. cbn [ev]. unfold reg_ev. destruct (Nat.ltb_spec (49 + k) 32) as [Q|Q]; [lia|]. replace (49 + k - 32)%nat with (17 + k)%nat by lia.
    rewrite app_nth2 by (cbn [length]; lia). cbn [length]. replace (17 + k - 17)%nat with k by lia. rewrite Hn. reflexivity. }
  rewrite Hev. apply u64_of_Z. exact Hz.
Qed.

Lemma winf_ok : forall (C : PSK.consts) wptrx stx morex seg wlen ch (winb : list Z),
  PSK.c_hull_lo C = 0x10000 /\ PSK.c_hull_hi C = 0xf8000 -> PSK.c_scr C = SCR ->
  In (ch, 16384) LBo -> ch <= seg -> seg + wlen <= ch + 16384 ->
  L5.bytes_at RSEGS M seg winb -> Z.of_nat (length winb) = wlen -> L5.defined M seg wlen -> ebf 1%nat = map (Z_to_bv 8) winb -> nth 1 xv 0 = seg -> nth 2 xv 0 = wlen ->
  know_ok RSEGS E0 M (SPK.win_f C Pb Vb Eb (EVar 2) (EVar 50) (EVar 51) (X0w wptrx stx morex)).
Proof.
  intros C wptrx stx morex seg wlen ch winb (C4a & C4b) C6 Hch Hc1 Hc2 Hwb Hwl Hwd Heb.
  pose proof UU as (U2' & UP & UE & UV). pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof NUM as (BR1 & BR2 & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  destruct INST as (HIok & LAY & HH & Hentry & HS1 & HS2 & HPA & HWF & HLV & HSZ & N10 & HVIS & HEC & HLS & HPC & OP & OV & OE & AP1 & AP2 & AP3 & _).
  destruct OP as (OP1 & OP2 & OP3), OV as (OV1 & OV2 & _), OE as (OE1 & OE2 & _). fold SCR in HS1.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  assert (I1 : In (bptr, bcap) (PML.ps_blocks ps ++ LBo)) by (left; reflexivity).
  assert (I2 : In (sb, scap) (PML.ps_blocks ps ++ LBo)) by (right; left; reflexivity).
  assert (I3 : In (ch, 16384) (PML.ps_blocks ps ++ LBo)) by (right; right; exact Hch).
  destruct (Hwf _ I1) as (_ & _ & BA1). destruct (Hwf _ I2) as (_ & _ & BA2). destruct (Hwf _ I3) as (BR3 & _ & _). cbn [fst snd] in *.
  unfold PML.ps_blocks in Hnd. fold bptr bcap sb scap in Hnd. cbn [map fst app] in Hnd.
  inversion Hnd as [|x0 l0 Nn1 Nn2 EQ0]. clear EQ0. inversion Nn2 as [|x1 l1 Nn3 Nn4 EQ1]. clear EQ1.
  assert (Nch1 : ch <> bptr) by (intros X; apply Nn1; apply list_elem_of_In; right; apply in_map_iff; exists (ch, 16384); split; [exact X | exact Hch]).
  assert (Nch2 : ch <> sb) by (intros X; apply Nn3; apply list_elem_of_In; apply in_map_iff; exists (ch, 16384); split; [exact X | exact Hch]).
  pose proof (L5C.blocks_apart_in _ _ _ ch 16384 BA1 (L5C.in_lb_remove_neq bptr ch 16384 _ I3 Nch1)) as A2.
  pose proof (L5C.blocks_apart_in _ _ _ ch 16384 BA2 (L5C.in_lb_remove_neq sb ch 16384 _ I3 Nch2)) as A3.
  intros X1 X2.
  destruct BR1 as (P0 & P1 & P2 & P3 & P4), BR2 as (Q0 & Q1 & Q2 & Q3 & Q4), BR3 as (R0 & R1 & R2 & R3 & R4). unfold hl_ceil in *.
  rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in R1.
  assert (Hwl0 : 0 <= wlen) by (clear - Hwl; lia).
  assert (AR : 0 <= wlen <= 16384 /\ 4096 <= seg /\ seg + wlen <= hl_sptop L - 8388608 /\ (seg + wlen <= 0x10000 \/ 0xf8000 <= seg) /\
               (bptr + bcap <= seg \/ seg + wlen <= bptr) /\ (sb + scap <= seg \/ seg + wlen <= sb)).
  { clear - Hwl0 Hc1 Hc2 R0 R1 R4 A2 A3. lia. }
  assert (AS : hl_sptop L - 8388608 + SCR <= sp /\ sp <= P /\ sp <= E /\ sp <= V /\ 0 <= SCR <= 2 ^ 20 /\ hl_sptop L <= 2 ^ 47 /\ 0x7fff80000000 <= hl_sptop L).
  { clear - S6 S7 S4 OP1 OV1 OE1 HS1 HS2. lia. }
  assert (AB : 0 <= bptr /\ 0 <= bcap /\ bptr + bcap <= hl_sptop L - 8388608 /\ 0 <= sb /\ 0 <= scap /\ sb + scap <= hl_sptop L - 8388608 /\ bcap = 2 * k0 /\ bcap <= 2 ^ 27).
  { clear - P0 P3 P4 Q0 Q3 Q4 Hk N1. lia. }
  clear - AR AS AB X1 X2 U2' UP UE UV Heb Hwb Hwl Hwd C6 C4a C4b.
  destruct AR as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6). destruct AS as (AS1 & AS2 & AS3 & AS4 & AS5 & AS6 & AS7). destruct AB as (AB1 & AB2 & AB3 & AB4 & AB5 & AB6 & AB7 & AB8).
  assert (E50 : ev E0 50 = Z_to_bv 64 seg) by (unfold E0; cbn [ev reg_ev]; rewrite <- X1; reflexivity).
  assert (E51 : ev E0 51 = Z_to_bv 64 wlen) by (unfold E0; cbn [ev reg_ev]; rewrite <- X2; reflexivity).
  assert (ES : estart E0 (SA (EVar 50) 0) = seg) by (unfold estart; cbn [a_base a_off edenot]; rewrite E50, u64_of_Z by lia; lia).
  assert (EL : elenZ E0 (EVar 51) = wlen) by (unfold elenZ; cbn [edenot]; rewrite E51; apply u64_of_Z; lia).
  assert (ESP : forall q, estart E0 (SA (EVar 2) q) = sp + q) by (intros q; unfold estart; cbn [a_base a_off]; fold (uv E0 (EVar 2)); rewrite U2'; reflexivity).
  assert (ESB : forall b v q, uv E0 b = v -> estart E0 (SA b q) = v + q) by (intros b v q Hb; unfold estart; cbn [a_base a_off]; fold (uv E0 b); rewrite Hb; reflexivity).
  assert (ELL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  assert (U37 : uv E0 (EVar 37) = bptr) by (unfold PB.uv; cbn [edenot]; change (ev E0 37) with (Z_to_bv 64 bptr); apply u64_of_Z; lia).
  assert (U38 : uv E0 (EVar 38) = sb) by (unfold PB.uv; cbn [edenot]; change (ev E0 38) with (Z_to_bv 64 sb); apply u64_of_Z; lia).
  assert (EL40 : elenZ E0 (EVar 40) = scap) by (unfold elenZ; cbn [edenot]; change (ev E0 40) with (Z_to_bv 64 scap); apply u64_of_Z; lia).
  assert (ELK : elenZ E0 (APC.escale 2 (EVar 35)) = bcap).
  { unfold elenZ. fold (uv E0 (APC.escale 2 (EVar 35))). rewrite PB.uv_escale. unfold PB.uv. cbn [edenot]. change (ev E0 35) with (Z_to_bv 64 k0). rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia. }
  clear X1 X2.
  unfold SPK.win_f, know_ok. cbn [PSK.x_p PSK.x_k PSK.x_sb PSK.x_scap X0w]. rewrite C6. unfold PSK.hull, PSK.kdisj. rewrite C4a, C4b.
  repeat (apply Forall_cons); [.. | apply Forall_nil].
  - eapply CL5.kblob_intro with (bs := winb) (A := seg); [exact ES | rewrite EL; lia | lia | lia | lia | exact Heb | exact Hwb | rewrite Hwl; exact Hwd].
  - eapply CL5.kunk_intro; [exact ES | exact EL | lia | lia | lia | exact Hwd].
  - cbn [kentry_ok edenot]. rewrite E51, u64_of_Z by lia. lia.
  - cbn [kentry_ok edenot]. rewrite E50, u64_of_Z by lia. lia.
  - eapply CL5.kdisj_intro; [exact (ESP _) | exact (ELL SCR ltac:(lia)) | exact ES | exact EL | lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UP) | exact (ELL 272 ltac:(lia)) | exact ES | exact EL | lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UE) | exact (ELL 16 ltac:(lia)) | exact ES | exact EL | lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UV) | exact (ELL 48 ltac:(lia)) | exact ES | exact EL | lia].
  - eapply CL5.kdisj_intro; [exact ES | exact EL | exact (ESB _ _ _ U37) | exact ELK | lia].
  - eapply CL5.kdisj_intro; [exact ES | exact EL | exact (ESB _ _ _ U38) | exact EL40 | lia].
  - eapply CL5.kdisj_intro; [exact ES | exact EL | unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; reflexivity | exact (ELL (0xf8000 - 0x10000) ltac:(lia)) | lia].
Qed.

Lemma mw_le : match mw with Some (p, e) => p <= e | None => True end.
Proof. destruct INST as (_ & _ & _ & _ & _ & _ & HPA & _). exact (win_le M P _ HPA). Qed.

Lemma last_stack : PML.ps_more ps = true -> ~ PML.comment_or_cr (PML.ps_st ps) -> PML.ps_st ps <> PML.ST_STRING ->
  exists rest x, PML.ps_stack ps = rest ++ [x] /\ ((x = 0 /\ level = 0) \/ ((x = 8 \/ x = 14) /\ 1 <= level)) /\
  exists C, PML.ps_stack ps = PML.ST_ROOT :: C /\ Forall PML.is_container C /\ Z.of_nat (length C) = level /\ 0 <= level <= 1024.
Proof.
  intros Hmore Hncc Hnstr. destruct INST as (_ & _ & _ & _ & _ & _ & _ & HWF & _).
  destruct HWF as (Wn & n' & W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)). cbn [PML.ps_set_nst PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st] in *.
  destruct (W7 Hmore) as (W8 & W9 & _ & W11 & _).
  assert (HT : T = []).
  { unfold PML.transient in W11. destruct W11 as [(HT & _)|[(_ & X)|[(S & _ & _ & X)|(S & _ & _ & X)]]]; [exact HT | contradiction | contradiction |].
    exfalso. apply Hncc. right. exact X. }
  subst T. rewrite app_nil_r in W5. fold level in W8, W9.
  destruct (last_cases C) as [->|(C' & y & ->)].
  - exists [], 0. split; [exact W5|]. split; [left; split; [reflexivity | cbn in W8; lia]|]. exists []. split; [exact W5|]. split; [constructor | split; [exact W8 | exact W9]].
  - exists (PML.ST_ROOT :: C'), y. split; [rewrite W5; reflexivity|]. split.
    + right. pose proof W6 as W6'. apply Forall_app in W6' as [_ W6']. inversion W6' as [|y' l' Hy _]; subst. unfold PML.is_container, PML.ST_OBJECT, PML.ST_ARRAY in Hy.
      split; [exact Hy | rewrite length_app in W8; cbn [length] in W8; lia].
    + exists (C' ++ [y]). split; [exact W5|]. split; [exact W6 | split; [exact W8 | exact W9]].
Qed.
End Pt.
End SPT.
