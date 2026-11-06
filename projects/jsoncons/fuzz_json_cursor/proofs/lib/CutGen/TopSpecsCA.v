(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8L5DefsA PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module TPSA.
Section SpecsA.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.

Definition DETECT_SCR : Z := 64 + PMSA.MEMCMP_SCR.

Definition detect_json_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (ch k sp r : Z),
    PMSA.cps_asan L ar HI pc r sp DETECT_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R ch /\ PMSA.a1 R k /\ 1 <= k <= 16384 /\ In (ch, 16384) LB /\ shadow_blk M ch 16384 /\ L5.defined M ch k /\
                  PMLA.img_ro IC M /\ PMSA.stksh ar M sp DETECT_SCR)
      (fun R M R' M' LB' cr' LBk W => exists p', PMSA.a0 R' p' /\ ch <= p' <= ch + k /\ p' <= ch + 4 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).

Definition XSGETN_SCR : Z := 64 + PMSA.MEM_SCR.

Definition xsgetn_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (IS ch gp rdst sp r : Z) (rep : PML.srep),
    PMSA.cps_asan L ar HI pc r sp XSGETN_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R (IS + 16) /\ PMSA.a1 R ch /\ PMSA.a2 R 16384 /\
                  PMLA.isrc_at (hl_segs L) IC M IS rep gp rdst /\ PMLA.srep_sh M rep /\ PMLA.img_ro IC M /\ Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\
                  PMSA.fobj M FF IS 272 /\ In (ch, 16384) LB /\ shadow_blk M ch 16384 /\ L5.defined M ch 16384 /\
                  (forall b, In b (PML.srep_blocks rep) -> In b LB /\ fst b <> ch) /\ PMSA.stksh ar M sp XSGETN_SCR)
      (fun R M R' M' LB' cr' LBk W => exists k, PMSA.a0 R' k /\ k = Z.min 16384 (PML.srep_data (IS + 80) rep + Z.of_nat (length (PML.srep_chars rep)) - gp) /\
          PMLA.isrc_at (hl_segs L) IC M' IS rep (gp + k) rdst /\ PMLA.srep_sh M' rep /\ shadow_blk M' ch 16384 /\ L5.defined M' ch 16384 /\
          LB' = LB /\ cr' = cr /\ LBk = lb_remove ch LB /\ W = [(IS + 40, 8)]).

Definition rdr_atA (M : word -> option byte) (R IS V ch : Z) (bof : bool) : Prop :=
  PMLA.u64 (hl_segs L) M (R + 240) IS /\ PMLA.u64 (hl_segs L) M (R + 248) (IS + 16) /\ PMLA.u64 (hl_segs L) M (R + 264) ch /\ PMLA.u64 (hl_segs L) M (R + 272) 16384 /\
  (exists de, PMLA.u64 (hl_segs L) M (R + 280) de /\ ch <= de <= ch + 16384) /\ PMLA.u64 (hl_segs L) M (R + 288) 0 /\ PMLA.u8 (hl_segs L) M (R + 296) (PMLA.b2z bof) /\
  PMLA.u64 (hl_segs L) M (R + 304) (PMLA.VT_VISITOR IC) /\ PMLA.u64 (hl_segs L) M (R + 312) V /\
  (exists st0, PMLA.iosb_at (hl_segs L) IC M (R + 88) st0 (R + 24)) /\ PMLA.u64 (hl_segs L) M (R + 32) (PMLA.CLASSIC_IMP IC) /\ L5.defined M R 320.
Definition RCHUNK_SCR : Z := 48 + DETECT_SCR.
Definition WRC (Rr IS E : Z) : list L5.range :=
  [(Rr + 256, 8); (Rr + 280, 17); (IS + 40, 8); (IS + 152, 4); (E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES)].
Definition read_chunk_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (Rr IS V E ch gp rdst sp r : Z) (rep : PML.srep) (bof : bool) (g : PML.ls_state),
    PMSA.cps_asan L ar HI pc r sp RCHUNK_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R Rr /\ PMSA.a1 R E /\
                  rdr_atA M Rr IS V ch bof /\ PMLA.isrc_at (hl_segs L) IC M IS rep gp rdst /\ PMLA.srep_sh M rep /\ PMLA.img_ro IC M /\ Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\
                  PMLA.ec_at (hl_segs L) IC M E 0 /\ PMLA.ls_ok (hl_segs L) IC g M /\ g <> PML.LS0 /\
                  PMSA.fobj M FF Rr 592 /\ PMSA.fobj M FF IS 272 /\ PMSA.fobj M FF E 16 /\ PMLA.apart Rr 592 IS 272 /\ PMLA.apart Rr 592 E 16 /\ PMLA.apart IS 272 E 16 /\
                  In (ch, 16384) LB /\ shadow_blk M ch 16384 /\ L5.defined M ch 16384 /\ (forall b, In b (PML.srep_blocks rep) -> In b LB /\ fst b <> ch) /\
                  PMSA.stksh ar M sp RCHUNK_SCR)
      (fun R M R' M' LB' cr' LBk W => exists (p k gp' rdst' code : Z) (bof' : bool) (g' : PML.ls_state),
          PMSA.a0 R' p /\ PMSA.a1 R' k /\ 0 <= p /\ p + k < 2 ^ 64 /\ 0 <= k <= 16384 /\ (0 < k -> ch <= p /\ p + k <= ch + 16384) /\
          rdr_atA M' Rr IS V ch bof' /\ PMLA.isrc_at (hl_segs L) IC M' IS rep gp' rdst' /\ PMLA.srep_sh M' rep /\ gp <= gp' /\ k <= gp' - gp /\ (code = 0 -> k = 0 -> rdst' = 2) /\
          PMLA.ec_at (hl_segs L) IC M' E code /\ PMLA.ls_ok (hl_segs L) IC g' M' /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\
          shadow_blk M' ch 16384 /\ L5.defined M' ch 16384 /\
          LB' = LB /\ cr' = cr /\ LBk = lb_remove ch LB /\ W = WRC Rr IS E).

Definition ps_reset (ps : PML.pstate) : PML.pstate :=
  PML.PS PML.ST_START (PML.ps_sst ps) (PML.ps_nst ps) true false 0 [PML.ST_ROOT] (PML.ps_sb ps) (PML.ps_scap ps) (PML.ps_bcap ps) (PML.ps_bptr ps) (PML.ps_buf ps) (PML.ps_win ps).
Definition RESET_SCR : Z := 48 + PMSA.VPUSH_SCR.
Definition WRS (P : Z) : list L5.range := [(P + 144, 4); (P + 160, 24); (P + 208, 1); (P + 211, 2); (P + 248, 24)].
Definition reset_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (P sp r : Z) (ps : PML.pstate),
    PMSA.cps_asan L ar HI pc r sp RESET_SCR LB FF LK cr A 4
      (fun R M => PMSA.a0 R P /\ PMLA.parser_at (hl_segs L) IC M P ps /\ PMLA.parser_sh M ps /\ (forall b, In b (PML.ps_blocks ps) -> In b LB) /\
                  PML.ps_bptr ps <> PML.ps_sb ps /\ 0 < PML.ps_scap ps <= 4096 /\ PMSA.fobj M FF P 272 /\ PMSA.stksh ar M sp RESET_SCR)
      (fun R M R' M' LB' cr' LBk W => PMLA.parser_at (hl_segs L) IC M' P (ps_reset ps) /\ PMLA.parser_sh M' (ps_reset ps) /\
          LB' = LB /\ cr' = cr /\ LBk = lb_remove (PML.ps_sb ps) LB /\ W = WRS P).

Definition rstate (M : word -> option byte) (LBo : list (Z * Z)) (FF : list fframe) (cr : credit) (Rr IS V E ch kx bx : Z) (rep : PML.srep)
           (ps : PML.pstate) (gp rdst code : Z) (bof : bool) (g : PML.ls_state) (B : Z) : Prop :=
  rdr_atA M Rr IS V ch bof /\ PMLA.parser_at (hl_segs L) IC M (Rr + 320) ps /\ PMLA.parser_sh M ps /\ PML.wf_ps ps /\ PMLA.win_okA M LBo ps /\ PML.buf_bound ps B /\
  B <= gp - PML.srep_data (IS + 80) rep /\ PMLA.isrc_at (hl_segs L) IC M IS rep gp rdst /\ PMLA.srep_sh M rep /\ PMLA.vis_at (hl_segs L) IC M V /\
  PMLA.ec_at (hl_segs L) IC M E code /\ PMLA.ls_ok (hl_segs L) IC g M /\ g <> PML.LS0 /\ PMLA.pcredit_xA L cr ps kx bx /\
  In (ch, 16384) LBo /\ shadow_blk M ch 16384 /\ L5.defined M ch 16384 /\ (forall b, In b (PML.srep_blocks rep) -> In b LBo /\ fst b <> ch) /\ Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\
  PMSA.fobj M FF Rr 592 /\ PMSA.fobj M FF IS 272 /\ PMSA.fobj M FF V 8 /\ PMSA.fobj M FF E 16 /\
  PMLA.apart Rr 592 IS 272 /\ PMLA.apart Rr 592 V 8 /\ PMLA.apart Rr 592 E 16 /\ PMLA.apart IS 272 V 8 /\ PMLA.apart IS 272 E 16 /\ PMLA.apart V 8 E 16.
Definition RCDONE_SCR : Z := 128 + PMSA.PF_SCR.
Definition WRD (Rr IS E : Z) : list L5.range := [(Rr, 592); (IS, 272); (E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES); (hl_tp L - 164, 4)].

Definition rcheck_done_specA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r Rr IS V E ch gp rdst kx bx B : Z) (rep : PML.srep) (bof : bool) (g : PML.ls_state) (ps : PML.pstate),
    PMSA.cps_asan L ar HI pc r sp RCDONE_SCR (PML.ps_blocks ps ++ LBo) FF LK cr A 2
      (fun R M => PMSA.a0 R Rr /\ PMSA.a1 R E /\ sp mod 32 = 0 /\ PMSA.stksh ar M sp RCDONE_SCR /\ rstate M LBo FF cr Rr IS V E ch kx bx rep ps gp rdst 0 bof g B)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : PML.pstate) (code gp' rdst' : Z) (g' : PML.ls_state),
          PMLA.source_at (hl_segs L) IC M' Rr ch /\ PMLA.parser_at (hl_segs L) IC M' (Rr + 320) ps' /\ PMLA.parser_sh M' ps' /\ PMLA.isrc_at (hl_segs L) IC M' IS rep gp' rdst' /\
          PMLA.ec_at (hl_segs L) IC M' E code /\ PMLA.ls_ok (hl_segs L) IC g' M' /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\
          LB' = PML.ps_blocks ps' ++ LBo /\ LBk = lb_remove ch LBo /\ PMLA.pcredit_xA L cr' ps' kx bx /\ PML.wf_ps ps' /\ W = WRD Rr IS E).

Definition READNEXT_SCRA : Z := PMSA.READNEXT_SCR.
Definition read_next_specA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r Rr IS V E ch gp sb bptr kx bx : Z) (rep : PML.srep) (g : PML.ls_state),
    let ps := PMSA.ps_init sb bptr in
    PMSA.cps_asan L ar HI pc r sp READNEXT_SCRA (PML.ps_blocks ps ++ LBo) FF LK cr A 6
      (fun R M => PMSA.a0 R Rr /\ PMSA.a1 R E /\ sp mod 32 = 0 /\ PMSA.stksh ar M sp READNEXT_SCRA /\
                  PMSA.reader_preA L IC M LBo FF Rr IS V E ch rep gp 0 true ps /\ gp = PML.srep_data (IS + 80) rep /\
                  (forall b, In b (PML.srep_blocks rep) -> fst b <> ch) /\ Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\ PMLA.ls_ok (hl_segs L) IC g M /\ g <> PML.LS0 /\ PMLA.pcredit_xA L cr ps kx bx)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : PML.pstate) (code gp' rdst' : Z) (bof' : bool) (g' : PML.ls_state) (B' : Z),
          rstate M' LBo FF cr' Rr IS V E ch kx bx rep ps' gp' rdst' code bof' g' B' /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\
          LB' = PML.ps_blocks ps' ++ LBo /\ LBk = lb_remove ch LBo /\ W = WRD Rr IS E).

Definition HARN_SCR : Z := 16384.
Definition EMPTY_A11 : Z := 0x68f020.
Definition harness_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r ptr : Z) (txt : list Z) (g : PML.ls_state),
    let n := Z.of_nat (length txt) in
    PMSA.cps_asan L ar HI pc r sp HARN_SCR LB FF LK cr A PMSA.LIB_FRAMES
      (fun R M => PMSA.a0 R ptr /\ PMSA.a1 R n /\ n < 2 ^ 26 /\ sp mod 16 = 0 /\ PMSA.stksh ar M sp HARN_SCR /\
                  ((txt = [] /\ ptr = EMPTY_A11) \/ (0 < n /\ In (ptr, n) LB)) /\ L5.bytes_at (hl_segs L) M ptr txt /\ L5.defined M ptr n /\ (0 < n -> shadow_blk M ptr n) /\
                  PMLA.ls_ok (hl_segs L) IC g M /\
                  28 * hl_k_per_malloc L <= fst cr /\ hl_b_lin L * (2 * n + 2 ^ 28 + 32768) + 28 * hl_b_overhead L <= snd cr    )
      (fun R M R' M' LB' cr' LBk W => exists g' : PML.ls_state,
          PMSA.a0 R' 0 /\ PMLA.ls_ok (hl_segs L) IC g' M' /\ (g' = PML.LS1 \/ g' = PML.J) /\ LB' = LB /\ LBk = LB /\
          fst cr - 28 * hl_k_per_malloc L <= fst cr' /\ snd cr - (hl_b_lin L * (2 * n + 2 ^ 28 + 32768) + 28 * hl_b_overhead L) <= snd cr' /\
          W = PMSA.foot_ranges IC ++ [(hl_tp L - 164, 4)]).
End SpecsA.
End TPSA.
