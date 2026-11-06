(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmCurDefs PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMCSA.
Definition mem := (word -> option byte).
Definition pstate := PML.pstate.

Definition PC_HARNESS : Z := 0xaf184.
Definition PC_CURSOR_CTOR : Z := 0xafce4.
Definition PC_CURSOR_CTOR_MAIN : Z := 0xc8124.
Definition PC_SRC_CTOR : Z := 0xc988c.
Definition PC_PARSER_CTOR : Z := 0xc8e00.
Definition PC_OPTS_DTOR : Z := 0xc89b0.
Definition PC_READ_NEXT_C : Z := 0xb3754.
Definition PC_GET_STRING : Z := 0xcc934.
Definition PC_STRINIT2 : Z := 0xce6b0.
Definition PC_CSTR_CTOR : Z := 0xd16b4.
Definition PC_WRAP_STRLEN : Z := 0x6a54c.
Definition PC_LOCALECONV : Z := 0x134e08.
Definition PC_SET_EC2 : Z := 0xc97b4.
Definition PC_CONV_EC : Z := 0xb1be0.
Definition PC_FROM_INT_U64 : Z := 0xccf40.      Definition PC_FROM_INT_I64 : Z := 0xcd580.      Definition PC_WRITE_DOUBLE : Z := 0xcdc30.
Definition VT_CURSOR : Z := 0x14ce88.           Definition VT_CURSOR_SER : Z := 0x14cf60.
Definition STR_TRUE : Z := 0x25f00.  Definition STR_FALSE : Z := 0x25f20.  Definition STR_NULL : Z := 0x25f40.
Definition CURSOR_SIZE : Z := 656.

Definition undelivered (IS : Z) (rep : PML.srep) (gp : Z) : Z := PML.srep_data (IS + 80) rep + Z.of_nat (length (PML.srep_chars rep)) - gp.
Definition rn_bound (ps : pstate) (IS : Z) (rep : PML.srep) (gp B : Z) : Prop :=
  Z.of_nat (length (PML.ps_buf ps)) + PML.winlen ps + PML.buf_need ps + undelivered IS rep gp <= B /\ B < 2 ^ 26 /\ 0 <= PML.winlen ps.
Definition conv_ok (e : PMCUR.sevent) : Prop := match e with PMCUR.EvBeginObj | PMCUR.EvEndObj | PMCUR.EvBeginArr | PMCUR.EvEndArr => False | _ => True end.

Definition ev_len (e : PMCUR.sevent) : Z := match e with PMCUR.EvStr _ n | PMCUR.EvKey _ n => n | _ => 0 end.

Section SpecsCA.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.

Definition src_atA (M : mem) (S IS ch : Z) (bof : bool) : Prop :=
  PMLA.u64 (hl_segs L) M (S + 240) IS /\ PMLA.u64 (hl_segs L) M (S + 248) (IS + 16) /\ PMLA.u64 (hl_segs L) M (S + 264) ch /\ PMLA.u64 (hl_segs L) M (S + 272) 16384 /\
  (exists de, PMLA.u64 (hl_segs L) M (S + 280) de /\ ch <= de <= ch + 16384) /\ PMLA.u64 (hl_segs L) M (S + 288) 0 /\ PMLA.u8 (hl_segs L) M (S + 296) (PMLA.b2z bof) /\
  (exists st0, PMLA.iosb_at (hl_segs L) IC M (S + 88) st0 (S + 24)) /\ PMLA.u64 (hl_segs L) M (S + 32) (PMLA.CLASSIC_IMP IC).

Definition rdc_atA (M : mem) (S IS ch : Z) (bof : bool) : Prop := src_atA M S IS ch bof /\ L5.defined M S 320.

Definition cursor_atA (M : mem) (C IS ch : Z) (bof dn : bool) (ps : pstate) : Prop :=
  src_atA M (C + 8) IS ch bof /\ PMLA.parser_at (hl_segs L) IC M (C + 320) ps /\ PMLA.vis_at (hl_segs L) IC M (C + 592) /\ PMLA.u8 (hl_segs L) M (C + 640) (PMLA.b2z dn) /\ L5.defined M C CURSOR_SIZE.

Definition evcA (M : mem) (V lv0 : Z) (LBo : list (Z * Z)) (ps' : pstate) : Prop :=
  exists w0, match w0 with None => True | Some (p0, e0) => exists b, In (b, 16384) LBo /\ b <= p0 /\ e0 <= b + 16384 /\ L5.defined M p0 (e0 - p0) /\ shadow_blk M b 16384 end /\
             PMCUR.evp (hl_segs L) M V lv0 w0 ps'.

Definition rn_relA (ps ps' : pstate) (code : Z) (dn' : bool) (M' : mem) (V : Z) (LBo : list (Z * Z)) : Prop :=
  (PML.ps_st ps = PML.ST_ACCEPT -> code = 0 -> dn' = false /\ PML.ps_done ps' = true) /\
  (code = 0 -> dn' = false -> PML.ps_more ps' = false /\
     ((PML.ps_done ps' = true /\ PML.ps_st ps' = PML.ST_DONE) \/ (PMCUR.wf_c (PMCUR.ps_set_more ps' true) /\ evcA M' V (PML.ps_level ps) LBo ps'))).

Definition ec_conv_atA (M : mem) (E code : Z) : Prop := PMLA.u32 (hl_segs L) M E code /\ L5.defined M E 16 /\ PMLA.u64 (hl_segs L) M (E + 8) (PMLA.OBJ_CONV_CATEGORY IC).

Definition RCHUNK_SCR : Z := 8304.
Definition RN_SCR : Z := 224 + PMSA.PSOME_SCR.
Definition CCTOR_MAIN_SCR : Z := 128 + Z.max PMSA.CTOR_SCR RN_SCR.
Definition CCTOR_SCR : Z := 160 + CCTOR_MAIN_SCR.
Definition GETSTR_SCR : Z := 48 + 14336.

Definition RN_D : Z := 6.
Definition CCTOR_D : Z := 2 + RN_D.
Definition GET_D : Z := 6.
Definition WRC (S IS E : Z) : list L5.range :=
  [(S + 256, 8); (S + 280, 17); (IS + 40, 8); (IS + 152, 4); (E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES)].

Definition W_cur (C IS E : Z) : list L5.range :=
  [(C, CURSOR_SIZE); (IS, 272); (E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES); (hl_tp L - 164, 4)].

Definition set_ec2_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (E code sp r : Z) (g : PML.ls_state),
    PMSA.cps_asan L ar HI pc r sp PMSA.SETEC_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R E /\ PMSA.a1 R code /\ 1 <= code <= 31 /\ L5.defined M E 16 /\ PMLA.rstk ar sp E 16 /\ E mod 8 = 0 /\ shadow_zero M E 2 /\ PMSA.stksh ar M sp PMSA.SETEC_SCR /\
                  PMLA.ls_ok (hl_segs L) IC g M /\ g <> PML.LS0)
      (fun R M R' M' LB' cr' LBk W => PMLA.ec_at (hl_segs L) IC M' E code /\ PMLA.ls_ok (hl_segs L) IC (PML.regJ g) M' /\ LB' = LB /\ cr' = cr /\ LBk = LB /\
                                      W = [(E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES)]).

Definition conv_ec_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (E code sp r : Z) (g : PML.ls_state),
    PMSA.cps_asan L ar HI pc r sp PMSA.SETEC_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R E /\ PMSA.a1 R code /\ 1 <= code <= 31 /\ L5.defined M E 16 /\ PMSA.fobj M FF E 16 /\ PMSA.stksh ar M sp PMSA.SETEC_SCR /\
                  PMLA.ls_ok (hl_segs L) IC g M /\ g <> PML.LS0)
      (fun R M R' M' LB' cr' LBk W => ec_conv_atA M' E code /\ PMLA.ls_ok (hl_segs L) IC (PML.regC g) M' /\ PMSA.a0 R' E /\ LB' = LB /\ cr' = cr /\ LBk = LB /\
                                      W = [(E, 16); (PMLA.CONVCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES)]).

Definition cstr_ctor_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o src sp r : Z) (txt : list Z),
    PMSA.cps_asan L ar HI pc r sp (64 + PMSA.OPNEW_SCR) LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ PMSA.a1 R src /\
                  In (src, txt) [(STR_NULL, [110; 117; 108; 108]); (STR_TRUE, [116; 114; 117; 101]); (STR_FALSE, [102; 97; 108; 115; 101])] /\
                  PMLA.img_ro IC M /\ shadow_blk M src (Z.of_nat (length txt) + 1) /\ PMSA.fobj M FF o 24 /\ L5.defined M o 24 /\ PMSA.stksh ar M sp (64 + PMSA.OPNEW_SCR))
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = LB /\ PMLA.str_at_w (hl_segs L) M' o (PML.SShort txt) /\ LB' = LB /\ cr' = cr).

Definition read_chunk_c_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (S IS E ch gp rdst sp r : Z) (rep : PML.srep) (bof : bool) (g : PML.ls_state),
    PMSA.cps_asan L ar HI pc r sp RCHUNK_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R S /\ PMSA.a1 R E /\
                  rdc_atA M S IS ch bof /\ PMLA.isrc_at (hl_segs L) IC M IS rep gp rdst /\ PMLA.srep_sh M rep /\ PMLA.img_ro IC M /\ Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\
                  PMLA.ec_at (hl_segs L) IC M E 0 /\ PMLA.ls_ok (hl_segs L) IC g M /\ g <> PML.LS0 /\
                  PMSA.fobj M FF S 592 /\ PMSA.fobj M FF IS 272 /\ PMSA.fobj M FF E 16 /\ PMLA.apart S 592 IS 272 /\ PMLA.apart S 592 E 16 /\ PMLA.apart IS 272 E 16 /\
                  In (ch, 16384) LB /\ shadow_blk M ch 16384 /\ L5.defined M ch 16384 /\ (forall b, In b (PML.srep_blocks rep) -> In b LB /\ fst b <> ch) /\
                  PMSA.stksh ar M sp RCHUNK_SCR)
      (fun R M R' M' LB' cr' LBk W => exists (p k gp' rdst' code : Z) (bof' : bool) (g' : PML.ls_state),
          PMSA.a0 R' p /\ PMSA.a1 R' k /\ 0 <= p /\ p + k < 2 ^ 64 /\ 0 <= k <= 16384 /\ (0 < k -> ch <= p /\ p + k <= ch + 16384) /\
          rdc_atA M' S IS ch bof' /\ PMLA.isrc_at (hl_segs L) IC M' IS rep gp' rdst' /\ PMLA.srep_sh M' rep /\ gp <= gp' /\ k <= gp' - gp /\ (code = 0 -> k = 0 -> rdst' = 2) /\
          PMLA.ec_at (hl_segs L) IC M' E code /\ PMLA.ls_ok (hl_segs L) IC g' M' /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\
          shadow_blk M' ch 16384 /\ L5.defined M' ch 16384 /\
          LB' = LB /\ cr' = cr /\ LBk = lb_remove ch LB /\ W = WRC S IS E).

Definition read_next_specA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r C IS E ch gp rdst B kx bx : Z) (rep : PML.srep) (g : PML.ls_state) (bof : bool) (ps : pstate),
    PMSA.cps_asan L ar HI pc r sp RN_SCR (PML.ps_blocks ps ++ LBo) FF LK cr A RN_D
      (fun R M => PMSA.a0 R C /\ PMSA.a1 R (C + 592) /\ PMSA.a2 R E /\
                  cursor_atA M C IS ch bof false ps /\ PMCUR.wf_c (PMCUR.ps_set_more ps true) /\ PMLA.win_okA M LBo ps /\ PMLA.isrc_at (hl_segs L) IC M IS rep gp rdst /\
                  rn_bound (PMCUR.ps_set_more ps true) IS rep gp B /\ PMLA.ec_at (hl_segs L) IC M E 0 /\ In (ch, 16384) LBo /\ (forall b, In b (PML.srep_blocks rep) -> In b LBo /\ fst b <> ch) /\
                  Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\ PMLA.ls_ok (hl_segs L) IC g M /\ g <> PML.LS0 /\ PMLA.pcredit_xA L cr ps kx bx /\
                  PMSA.fobj M FF C CURSOR_SIZE /\ PMSA.fobj M FF IS 272 /\ PMSA.fobj M FF E 16 /\
                  PMLA.apart C CURSOR_SIZE IS 272 /\ PMLA.apart C CURSOR_SIZE E 16 /\ PMLA.apart IS 272 E 16 /\
                    PMLA.parser_sh M ps /\ PMLA.srep_sh M rep /\ shadow_blk M ch 16384 /\ L5.defined M ch 16384 /\ sp mod 32 = 0 /\ PMSA.stksh ar M sp RN_SCR)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code gp' rdst' : Z) (g' : PML.ls_state) (bof' dn' : bool),
          cursor_atA M' C IS ch bof' dn' ps' /\ PMLA.isrc_at (hl_segs L) IC M' IS rep gp' rdst' /\ rn_bound ps' IS rep gp' B /\ PMLA.ec_at (hl_segs L) IC M' E code /\
          PMLA.ls_ok (hl_segs L) IC g' M' /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\ PMCUR.wf_c ps' /\ PMLA.win_okA M' LBo ps' /\
          LB' = PML.ps_blocks ps' ++ LBo /\ LBk = lb_remove ch LBo /\ PMLA.pcredit_xA L cr' ps' kx bx /\
          W = W_cur C IS E /\
          rn_relA ps ps' code dn' M' (C + 592) LBo /\
            PMLA.parser_sh M' ps' /\ PMLA.srep_sh M' rep /\ shadow_blk M' ch 16384 /\ L5.defined M' ch 16384).

Definition cctor_preA (M : mem) (FF : list fframe) (cr : credit) (LB : list (Z * Z)) (C IS E sp scr kx bx : Z) (rep : PML.srep) (g : PML.ls_state) : Prop :=
  PMLA.isrc_at (hl_segs L) IC M IS rep (PML.srep_data (IS + 80) rep) 0 /\ PMLA.ec_at (hl_segs L) IC M E 0 /\ PMLA.img_ro IC M /\ PMSA.gloc_done L IC M /\
  PMLA.ls_ok (hl_segs L) IC g M /\ g <> PML.LS0 /\
  (forall b, In b (PML.srep_blocks rep) -> In b LB) /\ Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\
  PMSA.fobj M FF C CURSOR_SIZE /\ PMSA.fobj M FF IS 272 /\ PMSA.fobj M FF E 16 /\
  PMLA.apart C CURSOR_SIZE IS 272 /\ PMLA.apart C CURSOR_SIZE E 16 /\ PMLA.apart IS 272 E 16 /\ L5.defined M C CURSOR_SIZE /\
  ((PMLA.u8 (hl_segs L) M (PMLA.SYSCAT_GUARD IC) 0 /\ PMLA.u8 (hl_segs L) M (PMLA.SYSCAT_GUARD IC + 1) 0) \/ PMLA.u8 (hl_segs L) M (PMLA.SYSCAT_GUARD IC) 1) /\
  0 <= kx /\ 0 <= bx /\
  3 * hl_k_per_malloc L + PML.kleft (PMSA.ps_init 0 0) * hl_k_per_malloc L + kx <= fst cr /\
  hl_b_lin L * (16384 + 264 + 66) + 3 * hl_b_overhead L + hl_b_lin L * PML.bleft (PMSA.ps_init 0 0) + PML.kleft (PMSA.ps_init 0 0) * hl_b_overhead L + bx <= snd cr /\
    PMLA.srep_sh M rep /\ sp mod 32 = 0 /\ PMSA.stksh ar M sp scr.
Definition cctor_postA (LB : list (Z * Z)) (C IS E kx bx : Z) (rep : PML.srep) (g : PML.ls_state) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  exists (ch : Z) (ps' : pstate) (code gp' rdst' : Z) (g' : PML.ls_state) (bof' dn' : bool),
    cursor_atA M' C IS ch bof' dn' ps' /\ PMLA.isrc_at (hl_segs L) IC M' IS rep gp' rdst' /\ rn_bound ps' IS rep gp' (Z.of_nat (length (PML.srep_chars rep))) /\
    PMLA.ec_at (hl_segs L) IC M' E code /\ PMLA.ls_ok (hl_segs L) IC g' M' /\ (g' = g \/ g' = PML.regJ g) /\ PMCUR.wf_c ps' /\ PMLA.win_okA M' ((ch, 16384) :: LB) ps' /\
    PMLA.u8 (hl_segs L) M' (PMLA.SYSCAT_GUARD IC) 1 /\
    LB' = PML.ps_blocks ps' ++ (ch, 16384) :: LB /\ LBk = LB /\ PMLA.pcredit_xA L cr' ps' kx bx /\
    W = W_cur C IS E ++ [(PMLA.SYSCAT_GUARD IC, 2)] /\
    (code = 0 -> dn' = false -> PML.ps_more ps' = false /\
       ((PML.ps_done ps' = true /\ PML.ps_st ps' = PML.ST_DONE) \/ (PMCUR.wf_c (PMCUR.ps_set_more ps' true) /\ evcA M' (C + 592) 0 ((ch, 16384) :: LB) ps'))) /\
      PMLA.parser_sh M' ps' /\ PMLA.srep_sh M' rep /\ shadow_blk M' ch 16384 /\ L5.defined M' ch 16384 /\
    (forall b, In b (PML.srep_blocks rep) -> fst b <> ch).
Definition cursor_ctor_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (C IS E sp r kx bx : Z) (rep : PML.srep) (g : PML.ls_state),
    PMSA.cps_asan L ar HI pc r sp CCTOR_SCR LB FF LK cr A CCTOR_D
      (fun R M => PMSA.a0 R C /\ PMSA.a1 R IS /\ PMSA.a2 R E /\ cctor_preA M FF cr LB C IS E sp CCTOR_SCR kx bx rep g)
      (fun R M R' M' LB' cr' LBk W => cctor_postA LB C IS E kx bx rep g M' LB' cr' LBk W).

Definition a5 (R : bvmap 5 word) (v : Z) : Prop := getr R 15%bv = Z_to_bv 64 v.
Definition zeros (M : mem) (a n : Z) : Prop := forall j, 0 <= j < n -> byte_at M (a + j) 0.
Definition opts_atA (vto vto2 vtf : Z) (M : mem) (O : Z) : Prop :=
  L5.defined M O 240 /\ PMLA.u64 (hl_segs L) M O vto /\ PMLA.u32 (hl_segs L) M (O + 8) 0x10100 /\ PMLA.u64 (hl_segs L) M (O + 16) vtf /\
  PMLA.u64 (hl_segs L) M (O + 48) (O + 16) /\ PMLA.u64 (hl_segs L) M (O + 64) vto2 /\ zeros M (O + 72) 2 /\ zeros M (O + 80) 144 /\ PMLA.u32 (hl_segs L) M (O + 224) 1024.
Definition CCTOR_MAIN_D : Z := 1 + RN_D.
Definition cursor_main_specA (pc vto vto2 vtf : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (C IS O E sp r kx bx : Z) (rep : PML.srep) (g : PML.ls_state),
    PMSA.cps_asan L ar HI pc r sp CCTOR_MAIN_SCR LB FF LK cr A CCTOR_MAIN_D
      (fun R M => PMSA.a0 R C /\ PMSA.a3 R IS /\ PMSA.a4 R O /\ a5 R E /\ cctor_preA M FF cr LB C IS E sp CCTOR_MAIN_SCR kx bx rep g /\
                  opts_atA vto vto2 vtf M O /\ PMSA.fobj M FF O 240 /\ PMLA.apart C CURSOR_SIZE O 240 /\ PMLA.apart IS 272 O 240 /\ PMLA.apart E 16 O 240)
      (fun R M R' M' LB' cr' LBk W => cctor_postA LB C IS E kx bx rep g M' LB' cr' LBk W).

Definition ev_srcA (M : mem) (LB : list (Z * Z)) (e : PMCUR.sevent) : Prop :=
  match e with
  | PMCUR.EvStr p n | PMCUR.EvKey p n => 0 <= n < 2 ^ 26 /\ L5.defined M p n /\ aacc M p n /\ (n = 0 \/ exists b, In b LB /\ fst b <= p /\ p + n <= fst b + snd b)
  | _ => True
  end.

Definition s2_postA (capb : Z) (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M' : mem) (o : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists rep, PMLA.str_at_w (hl_segs L) M' o rep /\ PMLA.srep_sh M' rep /\ LB' = PML.srep_blocks rep ++ LB /\
    (PML.srep_blocks rep = [] -> cr' = cr) /\ (forall b, In b (PML.srep_blocks rep) -> PMSA.afresh L ar LB FF M' (fst b) (snd b) /\ cr' = adebit L cr (snd b) /\ snd b <= capb /\ snd b mod 2 = 0 /\ 24 <= snd b).
Definition get_string_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o V E sp r : Z) (e : PMCUR.sevent) (g : PML.ls_state),
    PMSA.cps_asan L ar HI pc r sp GETSTR_SCR LB FF LK cr A GET_D
      (fun R M => PMSA.a0 R o /\ PMSA.a1 R (V + 8) /\ PMSA.a3 R E /\
                  PMCUR.ev_at (hl_segs L) M V e /\ ev_srcA M LB e /\ L5.defined M V 48 /\ PMLA.ec_at (hl_segs L) IC M E 0 /\ PMLA.img_ro IC M /\ PMLA.ls_ok (hl_segs L) IC g M /\ g <> PML.LS0 /\
                  PMSA.fobj M FF o 24 /\ L5.defined M o 24 /\ PMSA.fobj M FF E 16 /\ PMLA.apart o 24 E 16 /\ PMLA.apart o 24 V 48 /\ PMLA.apart V 48 E 16 /\
                  acredit_ok L cr (Z.max 48 (match e with PMCUR.EvStr _ n | PMCUR.EvKey _ n => PML.str_cap n | _ => 0 end)) /\
                    PMSA.fobj M FF V 48 /\ PMSA.stksh ar M sp GETSTR_SCR /\ sp mod 32 = 0)
      (fun R M R' M' LB' cr' LBk W => exists (code : Z) (g' : PML.ls_state),
          s2_postA (Z.max 48 (match e with PMCUR.EvStr _ n | PMCUR.EvKey _ n => PML.str_cap n | _ => 0 end)) LB FF cr M' o LB' cr' /\ LBk = LB /\
          PMLA.u32 (hl_segs L) M' E code /\ L5.defined M' E 16 /\ PMLA.ls_ok (hl_segs L) IC g' M' /\
          ((conv_ok e /\ code = 0 /\ g' = g /\ PMLA.ec_at (hl_segs L) IC M' E 0) \/ (~ conv_ok e /\ code = 11 /\ g' = PML.regC g /\ ec_conv_atA M' E 11)) /\
          W = [(o, 24); (E, 16); (PMLA.CONVCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES); (hl_tp L - 164, 4)]).

Definition LIB_FRAMES_C : Z := 9.
Definition pm_creditA_c (n : Z) : credit := (32 * hl_k_per_malloc L, hl_b_lin L * (3 * n + 2 ^ 28 + 65536) + 32 * hl_b_overhead L).
Definition pm_layout_okA_c (Lay : lib_layoutA) : Prop :=
  lla_L Lay = L /\ PMSA.LIB_SCR <= lla_stack Lay /\ lla_stack Lay mod 16 = 0 /\ lla_foot Lay = PMLA.FOOT IC /\
  lla_junk Lay = [(hl_tp L - 164, hl_tp L - 160)] /\
  (forall k, In k PM_FS_CLASSES -> lla_frames Lay k = LIB_FRAMES_C /\ lla_leak Lay k = 0) /\
  (forall n, lla_credit Lay n = pm_creditA_c n) /\ PMLA.IMG_RO_HI IC <= lla_rw_lo Lay /\
  lla_atexit Lay = PMLA.ATEXIT_TAB IC /\ lla_hs0 Lay = PMLA.HS0 IC /\ lla_need_locks Lay = PMLA.NEED_LOCKS IC /\
  (forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ (PMLA.in_foot IC a /\ ~ PMLA.in_tab IC a /\ a <> PMLA.NEED_LOCKS IC) ->
             exists iv, In iv (lla_init_img Lay) /\ fst iv <= a < snd iv) /\
  (forall M : mem, (forall a, PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 -> M (Z_to_bv 64 a) = None) -> cell_is (hl_segs L) M (PMLA.LOCALE_LOCK IC) 4 0).
Definition lib_specA_c (Lay : lib_layoutA) : Prop := pm_layout_okA_c Lay -> PmLibIfaceA.lib_call_okA Lay ar SCFG HI (PMSA.pm_staticsA L IC).

Lemma lib_exit_okA_c : forall (Lay : lib_layoutA), pm_layout_okA_c Lay -> PmLibIfaceA.lib_exit_factsA Lay (PMSA.pm_staticsA L IC) (PMLA.ls_atexit IC).
Proof.
  intros Lay (HL & _ & _ & _ & _ & _ & _ & _ & HA & HH & HN & _) g M Hok. rewrite HA, HH, HN, HL. exact (PMLA.ls_ok_exit (hl_segs L) IC g M Hok).
Qed.

Lemma pm_layout_okA_c_fields : forall Lay, pm_layout_okA_c Lay ->
  lla_L Lay = L /\ PMSA.LIB_SCR <= lla_stack Lay /\ lla_stack Lay mod 16 = 0 /\ lla_foot Lay = PMLA.FOOT IC /\ lla_junk Lay = [(hl_tp L - 164, hl_tp L - 160)].
Proof. intros Lay (H1 & H2 & H3 & H4 & H5 & _). exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))). Qed.
End SpecsCA.
End PMCSA.
