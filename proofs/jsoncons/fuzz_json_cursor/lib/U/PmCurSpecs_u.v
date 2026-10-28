(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmCurDefs_u PmLibSpecs_u.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMCS.

Definition PC_CURSOR_CTOR : Z := 0x39ae8.
Definition PC_CURSOR_CTOR_MAIN : Z := 0x40e68.
Definition PC_SRC_CTOR : Z := 0x4173c.
Definition PC_NULL_IS_CTOR : Z := 0x417dc.
Definition PC_READ_NEXT_C : Z := 0x3b180.
Definition PC_GET_STRING : Z := 0x42ecc.
Definition PC_STRINIT2 : Z := 0x438b8.
Definition PC_CSTR_CTOR : Z := 0x45290.
Definition PC_STRLEN : Z := 0xb82f8.
Definition PC_LOCALECONV : Z := 0xa7d48.
Definition PC_SET_EC2 : Z := 0x416a8.
Definition PC_BYTES_STR : Z := 0x43180.
Definition VT_CURSOR : Z := 0xbd920.           Definition VT_CURSOR_SER : Z := 0xbd9f8.
Definition STR_NULL : Z := 0x1112a.  Definition STR_TRUE : Z := 0x11c42.  Definition STR_FALSE : Z := 0x10347.
Definition CURSOR_SIZE : Z := 656.

Definition src_at (M : mem) (S IS ch : Z) (bof : bool) : Prop :=
  u64 M (S + 240) IS /\ u64 M (S + 248) (IS + 16) /\ u64 M (S + 264) ch /\ u64 M (S + 272) 16384 /\
  (exists de, u64 M (S + 280) de /\ ch <= de <= ch + 16384) /\ u64 M (S + 288) 0 /\ u8 M (S + 296) (b2z bof) /\
  (exists st0, iosb_at M (S + 88) st0 (S + 24)) /\ u64 M (S + 32) CLASSIC_IMP.

Definition cursor_at (M : mem) (C IS ch : Z) (bof dn : bool) (ps : pstate) : Prop :=
  src_at M (C + 8) IS ch bof /\ parser_at M (C + 320) ps /\ vis_at M (C + 592) /\ u8 M (C + 640) (b2z dn) /\ L5.defined M C CURSOR_SIZE.

Definition undelivered (IS : Z) (rep : srep) (gp : Z) : Z := srep_data (IS + 80) rep + Z.of_nat (length (srep_chars rep)) - gp.

Definition rn_bound (ps : pstate) (IS : Z) (rep : srep) (gp B : Z) : Prop :=
  Z.of_nat (length (ps_buf ps)) + winlen ps + buf_need ps + undelivered IS rep gp <= B /\ B < 2 ^ 26 /\ 0 <= winlen ps.

Definition evc (M : mem) (V lv0 : Z) (LBo : list (Z * Z)) (ps' : pstate) : Prop :=
  exists w0, match w0 with None => True | Some (p0, e0) => exists b, In (b, 16384) LBo /\ b <= p0 /\ e0 <= b + 16384 /\ L5.defined M p0 (e0 - p0) end /\
             PMCUR.evp RSEGS M V lv0 w0 ps'.

Definition rn_rel (ps ps' : pstate) (code : Z) (dn' : bool) (M' : mem) (V : Z) (LBo : list (Z * Z)) : Prop :=
  (ps_st ps = ST_ACCEPT -> code = 0 -> dn' = false /\ ps_done ps' = true) /\
  (code = 0 -> dn' = false -> ps_more ps' = false /\
     ((ps_done ps' = true /\ ps_st ps' = ST_DONE) \/ (PMCUR.wf_c (PMCUR.ps_set_more ps' true) /\ evc M' V (ps_level ps) LBo ps'))).

Definition rdc_at (M : mem) (S IS ch : Z) (bof : bool) : Prop := src_at M S IS ch bof /\ L5.defined M S 304.
Definition RCHUNK_SCR : Z := 512.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.

Definition RN_SCR : Z := PMS.READNEXT_SCR STRTOD_SCR.
Definition CCTOR_MAIN_SCR : Z := 96 + Z.max (PMS.CTOR_SCR) RN_SCR.
Definition CCTOR_SCR : Z := 304 + CCTOR_MAIN_SCR.
Definition GETSTR_SCR : Z := 48 + 10240 + STRTOD_SCR.

Definition LIB_SCR_C : Z := 1040 + Z.max CCTOR_SCR (Z.max GETSTR_SCR (Z.max PMS.ISS_SCR (96 + PMS.OPDEL_SCR))).

Definition set_ec2_spec : Prop :=
  forall (E code sp r : Z) (g : ls_state),
    cps_pure PC_SET_EC2 r sp PMS.SETEC_SCR [(E, 16); (0xd4df8, 2); (0xf6848, 544)]
      (fun R M => entry L R M sp r PMS.SETEC_SCR /\ a0 R E /\ a1 R code /\ 1 <= code <= 31 /\ L5.defined M E 16 /\ obj_on_stack L sp E 16 /\ ls_ok g M /\ g <> LS0)
      (fun R M R' M' => ec_at M' E code /\ ls_ok (regJ g) M').

Definition strinit2_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o src sp r : Z) (txt : list Z),
    cps_heap L HI PC_STRINIT2 r sp (48 + PMS.OPNEW_SCR) LB cr
      (fun R M => entry L R M sp r (48 + PMS.OPNEW_SCR) /\ a0 R o /\ a1 R src /\ a2 R (Z.of_nat (length txt)) /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.bytes_at RSEGS M src txt /\ L5.defined M src (Z.of_nat (length txt)) /\ obj_on_stack L sp o 24 /\ L5.defined M o 24 /\
                  (txt = [] \/ exists b, In b LB /\ fst b <= src /\ src + Z.of_nat (length txt) <= fst b + snd b) /\
                  ((23 <= length txt)%nat -> credit_ok L cr (str_cap (Z.of_nat (length txt)))))
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = LB /\
          (((length txt <= 22)%nat /\ str_at_w M' o (SShort txt) /\ LB' = LB /\ cr' = cr)
        \/ ((23 <= length txt)%nat /\ exists p, let cap := str_cap (Z.of_nat (length txt)) in
             str_at_w M' o (SLong cap p txt) /\ L5C.fresh_block L LB M' p cap /\ LB' = (p, cap) :: LB /\ cr' = debit L cr cap))).

Definition cstr_ctor_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o src sp r : Z) (txt : list Z),
    cps_heap L HI PC_CSTR_CTOR r sp (64 + PMS.OPNEW_SCR) LB cr
      (fun R M => entry L R M sp r (64 + PMS.OPNEW_SCR) /\ a0 R o /\ a1 R src /\ In (src, txt) [(STR_NULL, [110; 117; 108; 108]); (STR_TRUE, [116; 114; 117; 101]); (STR_FALSE, [102; 97; 108; 115; 101])] /\
                  img_ro M /\ obj_on_stack L sp o 24 /\ L5.defined M o 24)
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = LB /\ str_at_w M' o (SShort txt) /\ LB' = LB /\ cr' = cr).

Definition read_chunk_c_spec : Prop :=
  forall (sp r S IS E ch gp rdst : Z) (rep : srep) (bof : bool) (g : ls_state),
    cps_pure PC_READ_CHUNK r sp RCHUNK_SCR [(S, 304); (IS, 272); (E, 16); (ch, 16384); (0xd4df8, 2); (0xf6848, 544)]
      (fun R M => entry L R M sp r RCHUNK_SCR /\ a0 R S /\ a1 R E /\
                  rdc_at M S IS ch bof /\ isrc_at M IS rep gp rdst /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\ Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\
                  obj_on_stack L sp S 592 /\ obj_on_stack L sp IS 272 /\ obj_on_stack L sp E 16 /\ apart S 592 IS 272 /\ apart S 592 E 16 /\ apart IS 272 E 16 /\
                  block_range L ch 16384 /\ L5.defined M ch 16384 /\
                  (forall b, In b (srep_blocks rep) -> block_range L (fst b) (snd b) /\ apart (fst b) (snd b) ch 16384))
      (fun R M R' M' => exists (p k gp' rdst' code : Z) (bof' : bool) (g' : ls_state),
          a0 R' p /\ a1 R' k /\ 0 <= p /\ p + k < 2 ^ 64 /\ 0 <= k <= 16384 /\ (0 < k -> ch <= p /\ p + k <= ch + 16384) /\
          rdc_at M' S IS ch bof' /\ isrc_at M' IS rep gp' rdst' /\ gp <= gp' /\ k <= gp' - gp /\ (code = 0 -> k = 0 -> rdst' = 2) /\
          ec_at M' E code /\ ls_ok g' M' /\ (g' = g \/ (g' = regJ g /\ code <> 0))).

Definition read_next_spec : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r C IS E ch gp rdst B kx bx : Z) (rep : srep) (g : ls_state) (bof : bool) (ps : pstate),
    cps_heap L HI PC_READ_NEXT_C r sp RN_SCR (ps_blocks ps ++ LBo) cr
      (fun R M => entry L R M sp r RN_SCR /\ a0 R C /\ a1 R (C + 592) /\ a2 R E /\
                  cursor_at M C IS ch bof false ps /\ PMCUR.wf_c (PMCUR.ps_set_more ps true) /\ win_ok M LBo ps /\ isrc_at M IS rep gp rdst /\
                  rn_bound (PMCUR.ps_set_more ps true) IS rep gp B /\ ec_at M E 0 /\ In (ch, 16384) LBo /\ (forall b, In b (srep_blocks rep) -> In b LBo /\ fst b <> ch) /\
                  Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\ ls_ok g M /\ g <> LS0 /\ pcredit_x L cr ps kx bx /\
                  obj_on_stack L sp C CURSOR_SIZE /\ obj_on_stack L sp IS 272 /\ obj_on_stack L sp E 16 /\
                  apart C CURSOR_SIZE IS 272 /\ apart C CURSOR_SIZE E 16 /\ apart IS 272 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code gp' rdst' : Z) (g' : ls_state) (bof' dn' : bool),
          cursor_at M' C IS ch bof' dn' ps' /\ isrc_at M' IS rep gp' rdst' /\ rn_bound ps' IS rep gp' B /\ ec_at M' E code /\
          ls_ok g' M' /\ (g' = g \/ (g' = regJ g /\ code <> 0)) /\ PMCUR.wf_c ps' /\ win_ok M' LBo ps' /\
          LB' = ps_blocks ps' ++ LBo /\ LBk = lb_remove ch LBo /\ pcredit_x L cr' ps' kx bx /\
          W = [(C, CURSOR_SIZE); (IS, 272); (E, 16); (0xd4df8, 2); (0xf6848, 544)] /\
          rn_rel ps ps' code dn' M' (C + 592) LBo).

Definition cursor_ctor_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (C IS E sp r kx bx : Z) (rep : srep) (g : ls_state),
    cps_heap L HI PC_CURSOR_CTOR r sp CCTOR_SCR LB cr
      (fun R M => entry L R M sp r CCTOR_SCR /\ a0 R C /\ a1 R IS /\ a2 R E /\
                  isrc_at M IS rep (srep_data (IS + 80) rep) 0 /\ ec_at M E 0 /\ img_ro M /\ PMS.gloc_done M /\ ls_ok g M /\ g <> LS0 /\
                  ((u8 M 0xd5030 0 /\ u8 M 0xd5031 0) \/ u8 M 0xd5030 1) /\
                  (forall b, In b (srep_blocks rep) -> In b LB) /\ Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\
                  obj_on_stack L sp C CURSOR_SIZE /\ obj_on_stack L sp IS 272 /\ obj_on_stack L sp E 16 /\
                  apart C CURSOR_SIZE IS 272 /\ apart C CURSOR_SIZE E 16 /\ apart IS 272 E 16 /\ L5.defined M C CURSOR_SIZE /\
                  0 <= kx /\ 0 <= bx /\
                  3 * hl_k_per_malloc L + kleft (PMS.ps_init 0 0) * hl_k_per_malloc L + kx <= fst cr /\
                  16384 + 264 + 66 + 3 * hl_b_overhead L + bleft (PMS.ps_init 0 0) + kleft (PMS.ps_init 0 0) * hl_b_overhead L + bx <= snd cr)
      (fun R M R' M' LB' cr' LBk W => exists (ch : Z) (ps' : pstate) (code gp' rdst' : Z) (g' : ls_state) (bof' dn' : bool),
          cursor_at M' C IS ch bof' dn' ps' /\ isrc_at M' IS rep gp' rdst' /\ rn_bound ps' IS rep gp' (Z.of_nat (length (srep_chars rep))) /\ ec_at M' E code /\
          ls_ok g' M' /\ (g' = g \/ g' = regJ g) /\ PMCUR.wf_c ps' /\ win_ok M' ((ch, 16384) :: LB) ps' /\ u8 M' 0xd5030 1 /\
          LB' = ps_blocks ps' ++ (ch, 16384) :: LB /\ LBk = LB /\ pcredit_x L cr' ps' kx bx /\
          W = [(C, CURSOR_SIZE); (IS, 272); (E, 16); (0xd4df8, 2); (0xf6848, 544); (0xd5030, 2)] /\
          (code = 0 -> dn' = false -> ps_more ps' = false /\
             ((ps_done ps' = true /\ ps_st ps' = ST_DONE) \/ (PMCUR.wf_c (PMCUR.ps_set_more ps' true) /\ evc M' (C + 592) 0 ((ch, 16384) :: LB) ps')))).

Definition ev_src (M : mem) (LB : list (Z * Z)) (e : PMCUR.sevent) : Prop :=
  match e with
  | PMCUR.EvStr p n | PMCUR.EvKey p n => 0 <= n < 2 ^ 26 /\ L5.defined M p n /\ (n = 0 \/ exists b, In b LB /\ fst b <= p /\ p + n <= fst b + snd b)
  | _ => True
  end.

Definition conv_ok (e : PMCUR.sevent) : Prop := match e with PMCUR.EvBeginObj | PMCUR.EvEndObj | PMCUR.EvBeginArr | PMCUR.EvEndArr => False | _ => True end.

Definition s2_post (capb : Z) (LB : list (Z * Z)) (cr : credit) (M' : mem) (o : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists rep, str_at_w M' o rep /\ LB' = srep_blocks rep ++ LB /\
    (srep_blocks rep = [] -> cr' = cr) /\ (forall b, In b (srep_blocks rep) -> L5C.fresh_block L LB M' (fst b) (snd b) /\ cr' = debit L cr (snd b) /\ snd b <= capb).
Definition get_string_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o V E sp r : Z) (e : PMCUR.sevent) (g : ls_state),
    cps_heap L HI PC_GET_STRING r sp GETSTR_SCR LB cr
      (fun R M => entry L R M sp r GETSTR_SCR /\ a0 R o /\ a1 R (V + 8) /\ a3 R E /\
                  PMCUR.ev_at RSEGS M V e /\ ev_src M LB e /\ L5.defined M V 48 /\ ec_at M E 0 /\ img_ro M /\ ls_ok g M /\ g <> LS0 /\
                  obj_on_stack L sp o 24 /\ L5.defined M o 24 /\ obj_on_stack L sp E 16 /\ obj_on_stack L sp V 48 /\ apart o 24 E 16 /\ apart o 24 V 48 /\ apart V 48 E 16 /\
                  credit_ok L cr (Z.max 48 (match e with PMCUR.EvStr _ n | PMCUR.EvKey _ n => str_cap n | _ => 0 end)))
      (fun R M R' M' LB' cr' LBk W => exists (code : Z) (g' : ls_state),
          s2_post (Z.max 48 (match e with PMCUR.EvStr _ n | PMCUR.EvKey _ n => str_cap n | _ => 0 end)) LB cr M' o LB' cr' /\ LBk = LB /\ u32 M' E code /\ L5.defined M' E 16 /\ ls_ok g' M' /\
          ((conv_ok e /\ code = 0 /\ g' = g) \/ (~ conv_ok e /\ code = 11 /\ g' = regC g)) /\
          W = [(o, 24); (E, 16); (0xd4df0, 2); (0xf6848, 544)]).

Definition pm_credit_c (n : Z) : credit := (32 * hl_k_per_malloc L, 3 * n + 2 ^ 28 + 65536 + 32 * hl_b_overhead L).
Definition pm_layout_ok_c (Lay : lib_layout) : Prop :=
  ll_heap Lay = L /\ ll_entry Lay = PC_LIB /\ ll_gp Lay = 0x10800 /\ LIB_SCR_C <= ll_stack Lay /\ ll_foot Lay = ll_foot_csrc /\
  (forall n, ll_credit Lay n = pm_credit_c n) /\ IMG_RO_HI <= ll_rw_lo Lay.
Definition lib_spec_c (Lay : lib_layout) : Prop := pm_layout_ok_c Lay -> PMS.lib_call_ok_fp HI Lay PMS.pm_statics.
End Specs.
End PMCS.
