(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibSpecsXA PmLibSpecsW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMXAW.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pay_hi (ev : PMES.eev) : Z :=
  match ev with
  | PMES.EvBegin _ | PMES.EvEnd => 0 | PMES.EvKey bs => PMES.esc_len bs
  | PMES.EvStr tag bs => if (tag =? 1) || (tag =? 2) || (tag =? 3) then PMES.len bs else PMES.esc_len bs
  | PMES.EvNull => 4 | PMES.EvBool b => if b then 4 else 5 | PMES.EvU64 | PMES.EvI64 => 20 | PMES.EvDbl => 28
  end.
Definition kmax (es : PMES.estate) (ev : PMES.eev) : Z := PMES.ev_ind es ev + pay_hi ev.
(* [comment removed for export] *)
Lemma ev_ind_nonneg : forall es ev, 0 <= PMES.ev_ind es ev.
Proof.
  assert (C : forall c, 0 <= PMES.comma c) by (intros c; unfold PMES.comma; destruct (0 <? PMES.ec_count c); lia).
  assert (N : forall es, 1 <= PMES.nl es) by (intros es; unfold PMES.nl, PMES.depth; lia).
  assert (P : forall es, 0 <= fst (PMES.pre_scalar es)).
  { intros [|c r]; cbn -[PMES.comma PMES.nl]; [lia|]. destruct (PMES.ec_arr c); cbn -[PMES.comma PMES.nl]; [|lia]. pose proof (C c). pose proof (N (c :: r)). lia. }
  assert (Q : forall ev, 0 <= PMES.quotes ev) by (intros ev; unfold PMES.quotes; destruct ev; try lia; destruct (_ || _); lia).
  intros es ev. destruct ev; unfold PMES.ev_ind.
  - destruct es as [|c r]; [lia|]. destruct (PMES.ec_arr c); [|lia]. pose proof (C c). pose proof (N (c :: r)). lia.
  - destruct es as [|c r]; [lia|]. destruct (PMES.ec_nla c); unfold PMES.depth; lia.
  - destruct es as [|c r]; [lia|]. pose proof (C c). pose proof (N (c :: r)). lia.
  - pose proof (P es). pose proof (Q (PMES.EvStr tag bs)). lia.
  - pose proof (P es). pose proof (Q PMES.EvNull). lia.
  - pose proof (P es). pose proof (Q (PMES.EvBool b)). lia.
  - pose proof (P es). pose proof (Q PMES.EvU64). lia.
  - pose proof (P es). pose proof (Q PMES.EvI64). lia.
  - pose proof (P es). pose proof (Q PMES.EvDbl). lia.
Qed.
Lemma ind_run_nonneg : forall ks es, 0 <= PMW.ind_run es ks.
Proof. induction ks as [|k r IH]; intros es; cbn -[PMW.ind_k PMW.step_k]; [lia|]. pose proof (ev_ind_nonneg es (PMW.eev_of k)). unfold PMW.ind_k. pose proof (IH (PMW.step_k es k)). lia. Qed.
(* [comment removed for export] *)
Lemma pay_ok_hi : forall ev pay, PMES.pay_ok ev pay -> pay <= pay_hi ev.
Proof. intros ev pay H. destruct ev; cbn in *; lia. Qed.
(* [comment removed for export] *)
Lemma esc_len_bound : forall bs, 0 <= PMES.esc_len bs <= 6 * PMES.len bs.
Proof.
  assert (C : forall c, 1 <= PMES.esc_cls c <= 6).
  { intros c. unfold PMES.esc_cls. destruct (existsb _ _); [lia|]. destruct (_ || _); lia. }
  unfold PMES.len. induction bs as [|b r IH]; cbn [PMES.esc_len fold_right length]; [lia|]. fold (PMES.esc_len r). pose proof (C b). lia.
Qed.
Lemma pay_hi_begin : forall a, pay_hi (PMES.EvBegin a) = 0.          Proof. reflexivity. Qed.
Lemma pay_hi_end : pay_hi PMES.EvEnd = 0.                            Proof. reflexivity. Qed.
Lemma pay_hi_null : pay_hi PMES.EvNull <= 5.                         Proof. cbn; lia. Qed.
Lemma pay_hi_bool : forall b, pay_hi (PMES.EvBool b) <= 5.           Proof. intros [|]; cbn; lia. Qed.
Lemma pay_hi_u64 : pay_hi PMES.EvU64 = 20.                           Proof. reflexivity. Qed.
Lemma pay_hi_i64 : pay_hi PMES.EvI64 = 20.                           Proof. reflexivity. Qed.
Lemma pay_hi_dbl : pay_hi PMES.EvDbl = 28.                           Proof. reflexivity. Qed.
Lemma pay_hi_key : forall bs, pay_hi (PMES.EvKey bs) <= 6 * PMES.len bs.
Proof. intros bs. cbn [pay_hi]. pose proof (esc_len_bound bs). lia. Qed.
Lemma pay_hi_str : forall tag bs, pay_hi (PMES.EvStr tag bs) <= 6 * PMES.len bs.
Proof. intros tag bs. cbn [pay_hi]. pose proof (esc_len_bound bs). unfold PMES.len in *. destruct (_ || _); lia. Qed.
Lemma pay_hi_raw : forall tag bs, tag = 2 \/ tag = 3 -> pay_hi (PMES.EvStr tag bs) = PMES.len bs.
Proof. intros tag bs [-> | ->]; reflexivity. Qed.
(* [comment removed for export] *)
Lemma kmax_kind : forall es ev, kmax es ev = PMW.ind_k es (PMW.kind_of ev) + pay_hi ev.
Proof. intros es ev. unfold kmax. rewrite PMW.ind_k_of. reflexivity. Qed.
(* [comment removed for export] *)
Lemma ind_raw_num : forall es tag bs, tag = 2 \/ tag = 3 -> PMES.ev_ind es (PMES.EvStr tag bs) = PMW.ind_k es PMW.EkNum /\ PMES.estep es (PMES.EvStr tag bs) = PMW.step_k es PMW.EkNum.
Proof. intros es tag bs [-> | ->]; split; reflexivity. Qed.

Section SpecsXAW.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Variable enc_invA : PMSA.mem -> Z -> Z -> PMES.eghost -> Prop.      (* [comment removed for export] *)
Variable VIS_SCRA : Z.
Variable VIS_D : Z.
Variable benc : PMES.eghost -> Z.
Variable eroomA : PMES.eghost -> PMES.eev -> Prop.
Variable RM : PMW.refmodel.                                          (* [comment removed for export] *)
Variable CL : Z.                                                     (* [comment removed for export] *)

Abbreviation cps_asan := (PMSA.cps_asan L ar HI).
Abbreviation pstate := PML.pstate.   Abbreviation mem := PMSA.mem.
(* [comment removed for export] *)
Abbreviation std_args := PMSA.std_args.   Abbreviation cur_args := PMSA.cur_args.   Abbreviation literal_rel := PMSA.literal_rel.   Abbreviation win_exhausted := PMSA.win_exhausted.
Abbreviation not_retreated := PMSA.not_retreated.   Abbreviation PF_SCR := PMSA.PF_SCR.   Abbreviation ENDNUM_SCR := PMSA.ENDNUM_SCR.   Abbreviation ESV_SCR := PMSA.ESV_SCR.
Abbreviation PSOME_SCR := PMSA.PSOME_SCR.   Abbreviation AFTERV_SCR := PMSA.AFTERV_SCR.   Abbreviation SKIPWS_SCR := PMSA.SKIPWS_SCR.   Abbreviation text_inA := PMSA.text_inA.
Abbreviation ec_at := (PMSA.ec_at L IC).   Abbreviation vis_at := (PMSA.vis_at L IC).
Abbreviation parser_at := (PMSA.parser_at L IC).   Abbreviation parser_sh := PMSA.parser_sh.   Abbreviation win_okA := PMSA.win_okA.   Abbreviation buf_bound_stale := PMSA.buf_bound_stale.
Abbreviation stksh := (PMSA.stksh ar).   Abbreviation fobj := PMSA.fobj.   Abbreviation a0 := PMSA.a0.   Abbreviation a1 := PMSA.a1.   Abbreviation a2 := PMSA.a2.   Abbreviation a3 := PMSA.a3.
Abbreviation a4 := PMSA.a4.   Abbreviation consumed := PMSA.consumed.   Abbreviation u8 := (PMSA.u8 L).   Abbreviation u32 := (PMSA.u32 L).   Abbreviation u64 := (PMSA.u64 L).   Abbreviation W_parE := (PMSA.W_parE L IC).   Abbreviation ls_ok := (PMSA.ls_ok L IC).
Abbreviation lits_ok := (PMXA.lits_ok L IC).   Abbreviation kenc := (PMXA.kenc L).   Abbreviation enc_sync := PMXA.enc_sync.   Abbreviation W_encA := (PMXA.W_encA IC).
Abbreviation PFXA_SCR := (PMXA.PFXA_SCR VIS_SCRA).   Abbreviation ESVXA_SCR := (PMXA.ESVXA_SCR VIS_SCRA).   Abbreviation ENDNUMXA_SCR := (PMXA.ENDNUMXA_SCR VIS_SCRA).
Abbreviation PSOMEXA_SCR := (PMXA.PSOMEXA_SCR VIS_SCRA).   Abbreviation DVXA2 := (PMXA.DVXA2 VIS_D).   Abbreviation DVXA3 := (PMXA.DVXA3 VIS_D).   Abbreviation DVXA4 := (PMXA.DVXA4 VIS_D).
Abbreviation DBEGXA := (PMXA.DBEGXA VIS_D).   Abbreviation DPSXA := (PMXA.DPSXA VIS_D).   Abbreviation DPNXA := (PMXA.DPNXA VIS_D).   Abbreviation DPSOMEXA := (PMXA.DPSOMEXA VIS_D).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition win_bytesA (M : mem) (ps : pstate) (w : list Z) : Prop :=
  match PML.ps_win ps with
  | None => w = []
  | Some (p, e) => L5.bytes_at (hl_segs L) M p w /\ Z.of_nat (length w) = e - p /\ Forall (fun b => 0 <= b <= 255) w
  end.
(* [comment removed for export] *)
Definition wroom (eg : PMES.eghost) (evs : list PMW.evk) (al : Z) : Prop := PMES.g_len eg + PMW.ind_run (PMES.g_es eg) evs + al <= CL.
Definition wroomr (eg : PMES.eghost) (rr : PMW.cres (PMW.rm_ctrl RM)) : Prop := wroom eg (PMW.r_evs rr) (PMW.r_allow rr).
Definition roomwP : Prop := forall (g : PMES.eghost) (ev : PMES.eev), PMES.g_len g + kmax (PMES.g_es g) ev <= CL -> eroomA g ev.
(* [comment removed for export] *)
Lemma wroom_mono : forall eg evs al al', wroom eg evs al -> al' <= al -> wroom eg evs al'.
Proof. unfold wroom; intros; lia. Qed.
Lemma wroom_app : forall eg evs1 evs2 al1 al2, wroom eg (evs1 ++ evs2) (al1 + al2) -> 0 <= PMW.ind_run (PMW.es_run (PMES.g_es eg) evs1) evs2 -> 0 <= al2 -> wroom eg evs1 al1.
Proof. unfold wroom; intros eg evs1 evs2 al1 al2 H H1 H2. rewrite PMW.ind_run_app in H. lia. Qed.
(* [comment removed for export] *)
Lemma wroom_shift : forall eg eg1 evs1 evs2 al1 al2 pay,
  wroom eg (evs1 ++ evs2) (al1 + al2) -> PMES.g_es eg1 = PMW.es_run (PMES.g_es eg) evs1 -> PMES.g_len eg1 = PMES.g_len eg + PMW.ind_run (PMES.g_es eg) evs1 + pay ->
  0 <= pay <= al1 -> wroom eg1 evs2 al2.
Proof. unfold wroom; intros eg eg1 evs1 evs2 al1 al2 pay H Hes Hlen Hp. rewrite PMW.ind_run_app in H. rewrite Hes, Hlen. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ptrans_gbxAW (f : PMW.fname) (MIn : PMW.rm_ctrl RM -> mem -> Z -> pstate -> Prop) (inp_of : pstate -> list Z -> list Z -> list Z)
           (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> PMES.eghost -> list Z -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E S2 B kx bx : Z) (g : PML.ls_state) (ps : pstate) (eg : PMES.eghost) (w x : list Z) (c : PMW.rm_ctrl RM),
    cps_asan pc r sp scr (PML.ps_blocks ps ++ LBo ++ PMES.g_lbv eg) FF LK cr A d
      (fun R M => Args R M LBo P V E ps eg x /\ (uar = true -> sp mod 32 = 0) /\ stksh M sp scr /\
                  PAin M P ps /\ parser_sh M ps /\ WFin ps /\ win_okA M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0 /\
                  enc_invA M V S2 eg /\ lits_ok M /\ enc_sync ps eg /\
                  0 <= kx /\ 0 <= bx /\ PMLA.pcredit_xA L cr ps (kx + kenc eg) (bx + benc eg) /\
                  fobj M FF P 272 /\ fobj M FF V PMES.ENC_SIZE /\ fobj M FF E 16 /\ fobj M FF S2 24 /\
                  PMLA.apart P 272 V PMES.ENC_SIZE /\ PMLA.apart P 272 E 16 /\ PMLA.apart V PMES.ENC_SIZE E 16 /\
                  PMLA.apart P 272 S2 24 /\ PMLA.apart V PMES.ENC_SIZE S2 24 /\ PMLA.apart S2 24 E 16 /\
                  win_bytesA M ps w /\ MIn c M P ps /\                                                                             (* [comment removed for export] *)
                  wroomr eg (PMW.rm_step RM f c (inp_of ps w x)))                                                                  (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
          PAout ps M' P ps' /\ parser_sh M' ps' /\ PML.wf_ps ps' /\ win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          enc_invA M' V S2 eg' /\ lits_ok M' /\ (code = 0 -> enc_sync ps' eg') /\
          LB' = PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = LBo /\ W = PMLA.W_parA IC P E ++ W_encA V S2 /\
          PMLA.pcredit_xA L cr' ps' (kx + kenc eg') (bx + benc eg') /\ Rel ps ps' code R' /\
          let rr := PMW.rm_step RM f c (inp_of ps w x) in                                                                          (* [comment removed for export] *)
          code = PMW.r_code rr /\
          PMES.g_es eg' = PMW.es_run (PMES.g_es eg) (PMW.r_evs rr) /\
          (exists pay, 0 <= pay <= PMW.r_allow rr /\ PMES.g_len eg' = PMES.g_len eg + PMW.ind_run (PMES.g_es eg) (PMW.r_evs rr) + pay) /\
          (code = 0 -> PMW.rm_match RM (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = PML.winlen ps - PML.winlen ps' /\ win_bytesA M' ps' (PMW.w_after RM rr w))).
Definition ptrans_gxAW f inp := ptrans_gbxAW f (PMW.rm_match RM) inp PML.wf_ps PML.buf_bound.
Definition ptransxAW f inp := ptrans_gxAW f inp parser_at (fun _ => parser_at).
Definition ptrans_curxAW f inp := ptrans_gxAW f inp parser_at (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' (PML.ps_win ps))).
(* [comment removed for export] *)
Definition ptrans_stalexAW f inp (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> PMES.eghost -> list Z -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbxAW f (PMW.rm_stale RM) inp PML.wf_ps_stale buf_bound_stale (fun M P ps => parser_at M P (PML.ps_set_win ps mw))
                 (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) pc scr d uar Args Rel.
Definition ptrans_gbxeAW (f : PMW.fname) (MIn : PMW.rm_ctrl RM -> mem -> Z -> pstate -> Prop) (inp_of : pstate -> list Z -> list Z -> list Z)
           (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> PMES.eghost -> list Z -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E S2 B kx bx : Z) (g : PML.ls_state) (ps : pstate) (eg : PMES.eghost) (w x : list Z) (c : PMW.rm_ctrl RM),
    cps_asan pc r sp scr (PML.ps_blocks ps ++ LBo ++ PMES.g_lbv eg) FF LK cr A d
      (fun R M => Args R M LBo P V E ps eg x /\ (uar = true -> sp mod 32 = 0) /\ stksh M sp scr /\
                  PAin M P ps /\ parser_sh M ps /\ WFin ps /\ win_okA M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0 /\
                  enc_invA M V S2 eg /\ lits_ok M /\ enc_sync ps eg /\
                  0 <= kx /\ 0 <= bx /\ PMLA.pcredit_xA L cr ps (kx + kenc eg) (bx + benc eg) /\
                  fobj M FF P 272 /\ fobj M FF V PMES.ENC_SIZE /\ fobj M FF E 16 /\ fobj M FF S2 24 /\
                  PMLA.apart P 272 V PMES.ENC_SIZE /\ PMLA.apart P 272 E 16 /\ PMLA.apart V PMES.ENC_SIZE E 16 /\
                  PMLA.apart P 272 S2 24 /\ PMLA.apart V PMES.ENC_SIZE S2 24 /\ PMLA.apart S2 24 E 16 /\
                  win_bytesA M ps w /\ MIn c M P ps /\                                                                             (* [comment removed for export] *)
                  wroomr eg (PMW.rm_step RM f c (inp_of ps w x)))                                                                  (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
          PAout ps M' P ps' /\ parser_sh M' ps' /\ PML.wf_ps ps' /\ win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          enc_invA M' V S2 eg' /\ lits_ok M' /\ (code = 0 -> enc_sync ps' eg') /\
          LB' = PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = LBo /\ W = W_parE P E ++ W_encA V S2 /\
          PMLA.pcredit_xA L cr' ps' (kx + kenc eg') (bx + benc eg') /\ Rel ps ps' code R' /\
          let rr := PMW.rm_step RM f c (inp_of ps w x) in                                                                          (* [comment removed for export] *)
          code = PMW.r_code rr /\
          PMES.g_es eg' = PMW.es_run (PMES.g_es eg) (PMW.r_evs rr) /\
          (exists pay, 0 <= pay <= PMW.r_allow rr /\ PMES.g_len eg' = PMES.g_len eg + PMW.ind_run (PMES.g_es eg) (PMW.r_evs rr) + pay) /\
          (code = 0 -> PMW.rm_match RM (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = PML.winlen ps - PML.winlen ps' /\ win_bytesA M' ps' (PMW.w_after RM rr w))).
Definition ptrans_gxeAW f inp := ptrans_gbxeAW f (PMW.rm_match RM) inp PML.wf_ps PML.buf_bound.
Definition ptransxeAW f inp := ptrans_gxeAW f inp parser_at (fun _ => parser_at).
Definition ptrans_curxeAW f inp := ptrans_gxeAW f inp parser_at (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' (PML.ps_win ps))).
Definition ptrans_stalexeAW f inp (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> PMES.eghost -> list Z -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbxeAW f (PMW.rm_stale RM) inp PML.wf_ps_stale buf_bound_stale (fun M P ps => parser_at M P (PML.ps_set_win ps mw))
                  (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) pc scr d uar Args Rel.

(* [comment removed for export] *)
Definition ptrans_gbAW (f : PMW.fname) (MIn : PMW.rm_ctrl RM -> mem -> Z -> pstate -> Prop) (inp_of : pstate -> list Z -> list Z -> list Z)
           (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> list Z -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : pstate) (w x : list Z) (c : PMW.rm_ctrl RM),
    cps_asan pc r sp scr (PML.ps_blocks ps ++ LBo) FF LK cr A d
      (fun R M => Args R M LBo P V E ps x /\ (uar = true -> sp mod 32 = 0) /\ stksh M sp scr /\
                  PAin M P ps /\ parser_sh M ps /\ WFin ps /\ win_okA M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0 /\
                  PMLA.pcredit_xA L cr ps kx bx /\ fobj M FF P 272 /\ fobj M FF V 8 /\ fobj M FF E 16 /\
                  PMLA.apart P 272 V 8 /\ PMLA.apart P 272 E 16 /\ PMLA.apart V 8 E 16 /\
                  win_bytesA M ps w /\ MIn c M P ps)                                                                                (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : PML.ls_state),
          PAout ps M' P ps' /\ parser_sh M' ps' /\ PML.wf_ps ps' /\ win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          LB' = PML.ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = PMLA.W_parA IC P E /\ PMLA.pcredit_xA L cr' ps' kx bx /\ Rel ps ps' code R' /\
          let rr := PMW.rm_step RM f c (inp_of ps w x) in                                                                          (* [comment removed for export] *)
          code = PMW.r_code rr /\ PMW.r_evs rr = [] /\
          (code = 0 -> PMW.rm_match RM (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = PML.winlen ps - PML.winlen ps' /\ win_bytesA M' ps' (PMW.w_after RM rr w))).
Definition ptrans_gbkAW (f : PMW.fname) (MIn : PMW.rm_ctrl RM -> mem -> Z -> pstate -> Prop) (inp_of : pstate -> list Z -> list Z -> list Z)
           (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> list Z -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : pstate) (w x : list Z) (c : PMW.rm_ctrl RM),
    cps_asan pc r sp scr (PML.ps_blocks ps ++ LBo) FF LK cr A d
      (fun R M => Args R M LBo P V E ps x /\ (uar = true -> sp mod 32 = 0) /\ stksh M sp scr /\
                  PAin M P ps /\ parser_sh M ps /\ WFin ps /\ win_okA M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0 /\
                  PMLA.pcredit_xA L cr ps kx bx /\ fobj M FF P 272 /\ fobj M FF V 8 /\ fobj M FF E 16 /\
                  PMLA.apart P 272 V 8 /\ PMLA.apart P 272 E 16 /\ PMLA.apart V 8 E 16 /\
                  win_bytesA M ps w /\ MIn c M P ps)                                                                                (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : PML.ls_state),
          PAout ps M' P ps' /\ parser_sh M' ps' /\ PML.wf_ps ps' /\ win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          LB' = PML.ps_blocks ps' ++ LBo /\ LBk = PML.ps_blocks ps ++ LBo /\ W = PMLA.W_parA IC P E /\ PMLA.pcredit_xA L cr' ps' kx bx /\ Rel ps ps' code R' /\
          let rr := PMW.rm_step RM f c (inp_of ps w x) in                                                                          (* [comment removed for export] *)
          code = PMW.r_code rr /\ PMW.r_evs rr = [] /\
          (code = 0 -> PMW.rm_match RM (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = PML.winlen ps - PML.winlen ps' /\ win_bytesA M' ps' (PMW.w_after RM rr w)) /\
          PML.ps_blocks ps' = PML.ps_blocks ps).
Definition ptrans_gAW f inp := ptrans_gbAW f (PMW.rm_match RM) inp PML.wf_ps PML.buf_bound.
Definition ptransAW f inp := ptrans_gAW f inp parser_at (fun _ => parser_at).
Definition ptrans_stalekAW f inp (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> list Z -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbkAW f (PMW.rm_stale RM) inp PML.wf_ps_stale buf_bound_stale (fun M P ps => parser_at M P (PML.ps_set_win ps mw))
                 (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) pc scr d uar Args Rel.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition begin_container_specXAW (f : PMW.fname) (pc kind st' : Z) : Prop :=
  ptransxAW f PMW.inp_win pc PFXA_SCR DBEGXA true (fun R M LBo P V E ps eg x => std_args R M P V E ps /\ PML.ps_more ps = true /\ ~ PML.comment_or_cr (PML.ps_st ps) /\ PML.ps_st ps <> PML.ST_STRING)
         (fun ps ps' code R' =>
            (code = 0 /\ PML.ps_level ps' = PML.ps_level ps + 1 /\ PML.ps_st ps' = st' /\ PML.ps_more ps' = true /\ PML.ps_stack ps' = PML.ps_stack ps ++ [kind] /\ PML.ps_win ps' = PML.ps_win ps)
            \/ (code = 5 /\ PML.ps_level ps = 1024 /\ PML.ps_win ps' = PML.ps_win ps)).
Definition begin_object_specXAW (pc : Z) := begin_container_specXAW PMW.FBeginObject pc PML.ST_OBJECT PML.ST_EXPECT_MEMBER_NAME_OR_END.
Definition begin_array_specXAW (pc : Z) := begin_container_specXAW PMW.FBeginArray pc PML.ST_ARRAY PML.ST_EXPECT_VALUE_OR_END.
Definition end_container_specXAW (f : PMW.fname) (pc kind : Z) : Prop :=
  ptransxAW f PMW.inp_win pc PFXA_SCR DVXA3 true (fun R M LBo P V E ps eg x => std_args R M P V E ps /\ PML.ps_more ps = true /\ ~ PML.comment_or_cr (PML.ps_st ps) /\ PML.ps_st ps <> PML.ST_STRING)
         (fun ps ps' code R' =>
            (code = 0 /\ PML.ps_level ps' = PML.ps_level ps - 1 /\ PML.ps_more ps' = true /\ (exists rest, PML.ps_stack ps = rest ++ [kind] /\ PML.ps_stack ps' = rest) /\
             PML.ps_st ps' = (if Z.eqb (PML.ps_level ps') 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\ PML.ps_win ps' = PML.ps_win ps)
            \/ (In code [20; 21; 22; 23] /\ PML.ps_win ps' = PML.ps_win ps)).
Definition end_object_specXAW (pc : Z) := end_container_specXAW PMW.FEndObject pc PML.ST_OBJECT.
Definition end_array_specXAW (pc : Z) := end_container_specXAW PMW.FEndArray pc PML.ST_ARRAY.
Definition parse_true_specXAW (pc : Z) : Prop :=
  ptrans_curxAW PMW.FParseTrue PMW.inp_win pc PFXA_SCR DVXA2 true (fun R M LBo P V E ps eg x => cur_args R M P V E ps /\ PML.ps_more ps = true /\ ~ win_exhausted ps /\ PML.is_expect (PML.ps_st ps))
         (fun ps ps' code R' => literal_rel ps ps' code /\ not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_false_specXAW (pc : Z) : Prop :=
  ptrans_curxAW PMW.FParseFalse PMW.inp_win pc PFXA_SCR DVXA2 true (fun R M LBo P V E ps eg x => cur_args R M P V E ps /\ PML.ps_more ps = true /\ ~ win_exhausted ps /\ PML.is_expect (PML.ps_st ps))
         (fun ps ps' code R' => literal_rel ps ps' code /\ not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_null_specXAW (pc : Z) : Prop :=
  ptransxAW PMW.FParseNull PMW.inp_win pc PFXA_SCR DVXA2 true (fun R M LBo P V E ps eg x => std_args R M P V E ps /\ PML.ps_more ps = true /\ ~ win_exhausted ps /\ PML.is_expect (PML.ps_st ps))
         (fun ps ps' code R' => literal_rel ps ps' code).
(* [comment removed for export] *)
Definition end_string_value_specXAW (pc : Z) : Prop :=
  ptrans_stalexAW PMW.FEndStringValue PMW.inp_aux pc ESVXA_SCR DVXA3 true
         (fun R M LBo P V E ps eg x => a0 R P /\ a3 R V /\ a4 R E /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_STRING /\
                              (exists t, u8 M (P + 220) t /\ 0 <= t <= 1) /\                                           (* [comment removed for export] *)
                              exists s len, a1 R s /\ a2 R len /\ 0 <= len < 2 ^ 26 /\ L5.defined M s len /\
                                            text_inA M (PML.ps_blocks ps ++ LBo) s len /\
                                            L5.bytes_at (hl_segs L) M s x /\ Z.of_nat (length x) = len /\ Forall (fun b => 0 <= b <= 255) x)      (* [comment removed for export] *)
         (fun ps ps' code R' =>
            (code = 0 /\ PML.ps_more ps' = true /\ PML.ps_level ps' = PML.ps_level ps /\
             In (PML.ps_st ps') [PML.ST_EXPECT_COLON; PML.ST_EXPECT_COMMA_OR_END; PML.ST_ACCEPT])
            \/ In code [25; 26; 27; 28; 29]).
Definition parse_string_specXAW (pc : Z) : Prop :=
  ptrans_curxAW PMW.FParseString PMW.inp_win pc PFXA_SCR DPSXA true (fun R M LBo P V E ps eg x => cur_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_STRING)
         (fun ps ps' code R' => not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code <> 0 \/ consumed ps ps' \/ win_exhausted ps) /\
                                (code = 0 -> PML.ps_more ps' = true /\ PML.ps_level ps' = PML.ps_level ps)).
(* [comment removed for export] *)
Definition end_number_specXAW (f : PMW.fname) (pc : Z) : Prop :=
  ptrans_stalexAW f PMW.inp_buf pc ENDNUMXA_SCR DVXA4 true (fun R M LBo P V E ps eg x => std_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER /\ PML.num_final (PML.ps_buf ps))
         (fun ps ps' code R' => (code = 0 /\ PML.ps_more ps' = true /\ PML.ps_st ps' = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
                                 PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps) \/ code = 19).
Definition end_integer_value_specXAW (pc : Z) := end_number_specXAW PMW.FEndInt pc.
Definition end_fraction_value_specXAW (pc : Z) : Prop :=
  ptrans_stalexeAW PMW.FEndFrac PMW.inp_buf pc ENDNUMXA_SCR DVXA4 true (fun R M LBo P V E ps eg x => std_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER /\ PML.num_final (PML.ps_buf ps))
         (fun ps ps' code R' => (code = 0 /\ PML.ps_more ps' = true /\ PML.ps_st ps' = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
                                 PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps) \/ code = 19).
Definition parse_number_specXAW (pc : Z) : Prop :=
  ptrans_curxeAW PMW.FParseNumber PMW.inp_win pc PFXA_SCR DPNXA true (fun R M LBo P V E ps eg x => cur_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER)
         (fun ps ps' code R' => not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code = 0 -> PML.ps_level ps' = PML.ps_level ps /\ PML.ps_more ps' = true /\ (PML.ps_st ps' = PML.ST_NUMBER -> win_exhausted ps') /\
                                             In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END])).
Definition parse_some_specXAW (pc : Z) : Prop :=
  ptransxeAW PMW.FParseSome PMW.inp_win pc PSOMEXA_SCR DPSOMEXA true (fun R M LBo P V E ps eg x => std_args R M P V E ps /\ PML.ps_more ps = true)
         (fun ps ps' code R' =>
            (code <> 0 \/ PML.ps_more ps' = false \/ win_exhausted ps') /\
            (PML.ps_st ps = PML.ST_ACCEPT -> code = 0 /\ PML.ps_more ps' = false /\ PML.ps_done ps' = true) /\
            (win_exhausted ps -> code = 0 -> PML.ps_more ps' = true -> In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR]) /\
            (code = 0 -> PML.ws_ok ps')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition skip_space_spec2AW (pc : Z) : Prop :=
  ptransAW PMW.FSkipSpace PMW.inp_win pc PF_SCR 4 false
    (fun R M (LBo : list (Z * Z)) P V E ps x => a0 R P /\ a1 R (P + 200) /\ PML.ws_ok ps /\ (if PML.ps_more ps then PML.is_expect (PML.ps_st ps) else PML.ps_st ps = PML.ST_DONE) /\
                             exists p e b, PML.ps_win ps = Some (p, e) /\ p < e /\ u8 M p b /\ In b [9; 10; 13; 32])
    (fun ps ps' code R' => code = 0 /\ consumed ps ps' /\ PML.ps_more ps' = PML.ps_more ps /\ PML.ws_ok ps' /\
                            ((PML.ps_st ps' = PML.ps_st ps /\ PML.ps_stack ps' = PML.ps_stack ps) \/
                             (PML.ps_st ps' = PML.ST_CR /\ win_exhausted ps' /\ PML.ps_stack ps' = PML.ps_stack ps ++ [PML.ps_st ps])) /\
                            PML.ps_level ps' = PML.ps_level ps).
Definition begin_member_specAW (pc : Z) : Prop :=
  ptransAW PMW.FBeginMember PMW.inp_win pc PF_SCR 3 true (fun R M LBo P V E ps x => a0 R P /\ a1 R E /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_EXPECT_COMMA_OR_END)
         (fun ps ps' code R' => code = 0 /\ PML.ps_more ps' = true /\ In (PML.ps_st ps') [PML.ST_EXPECT_MEMBER_NAME; PML.ST_EXPECT_VALUE] /\
                                PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps).
(* [comment removed for export] *)
Definition after_value_specAW (pc : Z) : Prop :=
  ptrans_stalekAW PMW.FAfterValue PMW.inp_win pc AFTERV_SCR 3 true (fun R M LBo P V E ps x => a0 R P /\ a1 R E /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER)
         (fun ps ps' code R' => code = 0 /\ PML.ps_more ps' = true /\ PML.ps_st ps' = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
                                PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps).
(* [comment removed for export] *)
Definition skip_whitespace_specAW (pc : Z) : Prop :=
  ptransAW PMW.FSkipWs PMW.inp_win pc SKIPWS_SCR 4 true (fun R M LBo P V E ps x => a0 R P /\ PML.ws_ok ps /\ (PML.ps_more ps = true -> win_exhausted ps))
         (fun ps ps' code R' => code = 0 /\ not_retreated ps ps' /\ PML.ps_more ps' = PML.ps_more ps /\ PML.ws_ok ps').
Definition parser_check_done_specAW (pc : Z) : Prop :=
  ptransAW PMW.FCheckDone PMW.inp_win pc PF_SCR 2 true (fun R M LBo P V E ps x => a0 R P /\ a1 R E)
         (fun ps ps' code R' => (code = 0 /\ win_exhausted ps' /\ PML.ps_more ps' = PML.ps_more ps /\ PML.ps_st ps' = PML.ps_st ps /\ PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps) \/ code = 4).
(* [comment removed for export] *)
Definition validate_specAW (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (s len sp r : Z) (txt : list Z),
    cps_asan pc r sp 128 LB FF LK cr A 0
      (fun R M => a0 R s /\ a1 R len /\ 0 <= len < 2 ^ 27 /\ L5.defined M s len /\ PMLA.img_ro IC M /\ text_inA M LB s len /\
                  L5.bytes_at (hl_segs L) M s txt /\ Z.of_nat (length txt) = len /\ Forall (fun b => 0 <= b <= 255) txt)                    (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => (exists q c, a0 R' q /\ getr R' 11%bv = Z_to_bv 64 c /\ s <= q <= s + len /\ 0 <= c <= 6 /\ c = PMW.rm_validate RM txt)      (* [comment removed for export] *) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wroomr_eq : forall eg rr, wroomr eg rr = wroom eg (PMW.r_evs rr) (PMW.r_allow rr).
Proof. intros; reflexivity. Qed.
End SpecsXAW.
End PMXAW.
