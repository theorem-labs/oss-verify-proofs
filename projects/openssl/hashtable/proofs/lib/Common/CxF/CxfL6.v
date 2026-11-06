(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore CxPlan CxfCarry CxfCarry2 CxfGc CxfRt.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxfExec CxfL1 CxfL2 CxfL3 CxfL4 CxfL5 CxfL14 CxfL13 CxfL15 CxfLeaf CxfNat.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CXFEL.
Import CXFE.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import AX2B.
Import AX2BL.
Import APC.
Import APCL.
Definition grows (i : instr) : bool :=
  match i with Store _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => true | _ => false end.
Lemma L_CXFEL_grows : @grows = @CXFE.grows.
Proof. unfold grows. reflexivity. Qed.

Definition se_br (bc : bctx) (e : sentry) : option (Z * Z) := match e with SE a _ _ => base_rangeB bc (a_base a) end.
Lemma L_CXFEL_se_br : @se_br = @CXFE.se_br.
Proof. unfold se_br. rewrite ?AX2BL.L_AX2BL_base_rangeB. reflexivity. Qed.

Definition ranges_apartQRb (bc : bctx) (r1 br2 : option (Z * Z)) (RQ RS : list positive)
           (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match r1, br2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartR bc RQ RS then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Lemma L_CXFEL_ranges_apartQRb : @ranges_apartQRb = @CXFE.ranges_apartQRb.
Proof. unfold ranges_apartQRb. rewrite ?AX2BL.L_AX2BL_kdisj_apartR, ?AX2BL.L_AX2BL_lin_apartB. reflexivity. Qed.

Fixpoint log_lookupQLb (bc : bctx) (log : list sentry) (lrs : list (list positive)) (lbr : list (option (Z * Z))) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) (q : option (option (Z * Z) * list positive)) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      let lrs' := match lrs with _ :: t => t | [] => [] end in
      let lbr' := match lbr with _ :: t => t | [] => [] end in
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupQLb bc rest lrs' lbr' rb rk n sx hints acc q
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let q' := match q with Some x => x | None => (base_rangeB bc rb, regs bc rb rk (Z.of_nat n)) end in
          let rs := match lrs with r :: _ => r | [] => regs bc kb kk (Z.of_nat w) end in
          let br := match lbr with r :: _ => r | [] => base_rangeB bc kb end in
          if ranges_apartQRb bc (fst q') br (snd q') rs rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupQLb bc rest lrs' lbr' rb rk n sx hints acc (Some q')
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupQLb bc rest lrs' lbr' rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) (Some q')
          end
      end
  end.
Lemma L_CXFEL_log_lookupQLb : @log_lookupQLb = @CXFE.log_lookupQLb.
Proof. unfold log_lookupQLb. rewrite ?L_CXFEL_ranges_apartQRb, ?AX2BL.L_AX2BL_base_rangeB, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_lit_of_bytes, ?AX2L.L_AX2L_log_bytes_lit, ?AX2L.L_AX2L_mkExt, ?AX2BL.L_AX2BL_regs, ?AX2L.L_AX2L_rel_lit. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Definition sym_readBIF (ss : sym_state) (bc : bctx) (kx : kix) (lrs : list (list positive)) (lbr : list (option (Z * Z))) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupQLb bc (s_log ss) lrs lbr (a_base a) (a_off a) n sx' (sc_hints scr) [] None with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.
Definition sym_stepBIF (bc : bctx) (kx : kix) (lrs : list (list positive)) (lbr : list (option (Z * Z))) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod CXLF.p64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readBIF ss bc kx lrs lbr scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBIF ss bc kx lrs lbr scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else SStop   
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readBIF ss bc kx lrs lbr scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.
Definition sym_stepXBIF (bc : bctx) (kx : kix) (lrs : list (list positive)) (lbr : list (option (Z * Z))) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBIF bc kx lrs lbr i ss scr with
  | SOk ss' scs scr' =>
      if CXNAT.lebF (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
Definition lrs_stepF (bc : bctx) (i : instr) (ss' : sym_state) (lrs : list (list positive)) : list (list positive) :=
  if grows i then match s_log ss' with e :: _ => regsE bc e :: lrs | [] => lrs end else lrs.
Definition lbr_stepF (bc : bctx) (i : instr) (ss' : sym_state) (lbr : list (option (Z * Z))) : list (option (Z * Z)) :=
  if grows i then match s_log ss' with e :: _ => se_br bc e :: lbr | [] => lbr end else lbr.
Variable IT : itab.
Fixpoint goF (bc : bctx) (kx : kix) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
         (lrs lck : list (list positive)) (lbr : list (option (Z * Z))) : sym_state * list (list positive) :=
  match fuel with
  | O => if s_clean ss then (ss, lrs) else (ck, lck)
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, lrs) else (ck, lck)) else
      match itab_lookup IT (s_pc ss) with
      | None => if s_clean ss then (ss, lrs) else (ck, lck)
      | Some i =>
          match sym_stepXBIF bc kx lrs lbr K i ss scr_nil with
          | SOk ss' [] _ =>
              let lrs' := lrs_stepF bc i ss' lrs in
              let lbr' := lbr_stepF bc i ss' lbr in
              if s_clean ss' then goF bc kx K f false stops ss' ss' lrs' lrs' lbr' else goF bc kx K f false stops ss' ck lrs' lck lbr'
          | _ => if s_clean ss then (ss, lrs) else (ck, lck)
          end
      end
  end.
Variable nx0 : nat.
Definition run_block_f (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok nx0 cs then
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in
    let ss0 := clr (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    let '(ss', lrs) := goF bc kx K fuel true stops ss0 ss0 [] [] [] in
    match CXFC2L.carryKFL2 bc (s_log ss') lrs (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Definition run_block_gc_f (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block_f K fuel stops cs with Some cs' => Some (CXFGL.cs_gcF nx0 cs') | None => None end.
Definition run_block_c (K : nat) (fuel : nat) (stops : list Z) (c : CXFRTL.rtc) (cs : acs) : option acs * CXFRTL.rtc :=
  if fresh_ok nx0 cs then
    let ss := a_ss cs in
    let bcc := CXFRTL.mkbc_c c (facts_of (s_know ss)) in
    let bc := fst bcc in
    let kx := mk_kix (s_know ss) in
    let ss0 := clr (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    let '(ss', lrs) := goF bc kx K fuel true stops ss0 ss0 [] [] [] in
    (match CXFC2L.carryKFL2 bc (s_log ss') lrs (s_know ss') [] with
     | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
     | _ => None
     end, snd bcc)
  else (None, c).
Definition run_block_gc_c (K : nat) (fuel : nat) (stops : list Z) (c : CXFRTL.rtc) (cs : acs) : option acs * CXFRTL.rtc :=
  let r := run_block_c K fuel stops c cs in
  (match fst r with Some cs' => Some (CXFGL.cs_gcF nx0 cs') | None => None end, snd r).
End WithSegs.
Lemma L_CXFEL_sym_readBIF : @sym_readBIF = @CXFE.sym_readBIF.
Proof. unfold sym_readBIF. rewrite ?L_CXFEL_log_lookupQLb, ?AX2BL.L_AX2BL_extKB, ?AX2BL.L_AX2BL_flat_scB, ?AX2BL.L_AX2BL_know_lookupABI. reflexivity. Qed.

Lemma L_CXFEL_sym_stepBIF : @sym_stepBIF = @CXFE.sym_stepBIF.
Proof. unfold sym_stepBIF. rewrite ?L_CXFEL_sym_readBIF, ?AX2BL.L_AX2BL_amo_alignedbB, ?AX2L.L_AX2L_amo_aluop, ?AX2BL.L_AX2BL_amo_newvalB, ?AX2L.L_AX2L_amo_sx, ?AX2L.L_AX2L_amo_sz, ?AX2BL.L_AX2BL_conc_exprB, ?AX2BL.L_AX2BL_decide_branchB, ?AX2BL.L_AX2BL_enum_branchB, ?AX2BL.L_AX2BL_flat_scB, ?AX2BL.L_AX2BL_mkAluKB, ?AX2L.L_AX2L_mkAluw, ?AX2BL.L_AX2BL_mkAluwKB, ?AX2BL.L_AX2BL_mkMdKB, ?AX2L.L_AX2L_mkMdw, ?AX2L.L_AX2L_msize_bytes, ?AX2L.L_AX2L_resv_inval, ?AX2L.L_AX2L_ridx, ?AX2L.L_AX2L_saddr_eqb, ?AX2L.L_AX2L_sjump, ?AX2L.L_AX2L_sr_get, ?AX2L.L_AX2L_sr_upd, ?AX2L.L_AX2L_sset, ?AX2BL.L_AX2BL_storeok_scB, ?AX2BL.L_AX2BL_to_saddrKB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CXFEL_sym_stepXBIF : @sym_stepXBIF = @CXFE.sym_stepXBIF.
Proof. unfold sym_stepXBIF. rewrite ?L_CXFEL_sym_stepBIF, ?AX2L.L_AX2L_cap_rd, ?AX2BL.L_AX2BL_x_filterB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CXFEL_lrs_stepF : @lrs_stepF = @CXFE.lrs_stepF.
Proof. unfold lrs_stepF. rewrite ?L_CXFEL_grows, ?AX2BL.L_AX2BL_regsE. reflexivity. Qed.

Lemma L_CXFEL_lbr_stepF : @lbr_stepF = @CXFE.lbr_stepF.
Proof. unfold lbr_stepF. rewrite ?L_CXFEL_grows, ?L_CXFEL_se_br. reflexivity. Qed.

Lemma L_CXFEL_goF : @goF = @CXFE.goF.
Proof. unfold goF. rewrite ?L_CXFEL_sym_stepXBIF, ?L_CXFEL_lrs_stepF, ?L_CXFEL_lbr_stepF, ?AX2L.L_AX2L_itab_lookup, ?AX2L.L_AX2L_s_clean, ?AX2L.L_AX2L_scr_nil. reflexivity. Qed.

Lemma L_CXFEL_run_block_f : @run_block_f = @CXFE.run_block_f.
Proof. unfold run_block_f. rewrite ?L_CXFEL_goF, ?CXFC2L.L_CXFC2L_carryKFL2, ?AX2L.L_AX2L_clr, ?AX2L.L_AX2L_facts_of, ?APCL.L_APCL_fresh_ok, ?AX2BL.L_AX2BL_mk_kix, ?APCL.L_APCL_mk_ss, ?AX2BL.L_AX2BL_mkbc, ?APCL.L_APCL_with_ss. reflexivity. Qed.

Lemma L_CXFEL_run_block_gc_f : @run_block_gc_f = @CXFE.run_block_gc_f.
Proof. unfold run_block_gc_f. rewrite ?L_CXFEL_run_block_f, ?CXFGL.L_CXFGL_cs_gcF. reflexivity. Qed.

Lemma L_CXFEL_run_block_c : @run_block_c = @CXFE.run_block_c.
Proof. unfold run_block_c. rewrite ?L_CXFEL_goF, ?CXFC2L.L_CXFC2L_carryKFL2, ?AX2L.L_AX2L_clr, ?AX2L.L_AX2L_facts_of, ?APCL.L_APCL_fresh_ok, ?AX2BL.L_AX2BL_mk_kix, ?APCL.L_APCL_mk_ss, ?CXFRTL.L_CXFRTL_mkbc_c, ?CXFRTL.L_CXFRTL_rtc, ?APCL.L_APCL_with_ss. reflexivity. Qed.

Lemma L_CXFEL_run_block_gc_c : @run_block_gc_c = @CXFE.run_block_gc_c.
Proof. unfold run_block_gc_c. rewrite ?L_CXFEL_run_block_c, ?CXFGL.L_CXFGL_cs_gcF, ?CXFRTL.L_CXFRTL_rtc. reflexivity. Qed.

Definition RB_c (segs : list Segment) (IT : itab) (GC : bool) (KC bfuel : nat) (c : CXFRTL.rtc) (gb : nat) (stops : list Z) (cs : acs) : option acs * CXFRTL.rtc :=
  if GC then run_block_gc_c segs IT gb KC bfuel stops c cs else run_block_c segs IT gb KC bfuel stops c cs.
Lemma L_CXFEL_RB_c : @RB_c = @CXFE.RB_c.
Proof. unfold RB_c. rewrite ?L_CXFEL_run_block_c, ?L_CXFEL_run_block_gc_c, ?AX2L.L_AX2L_itab, ?CXFRTL.L_CXFRTL_rtc. reflexivity. Qed.

Definition RB_f (segs : list Segment) (IT : itab) (GC : bool) (KC bfuel : nat) (gb : nat) (stops : list Z) (cs : acs) : option acs :=
  if GC then run_block_gc_f segs IT gb KC bfuel stops cs else run_block_f segs IT gb KC bfuel stops cs.
Lemma L_CXFEL_RB_f : @RB_f = @CXFE.RB_f.
Proof. unfold RB_f. rewrite ?L_CXFEL_run_block_f, ?L_CXFEL_run_block_gc_f, ?AX2L.L_AX2L_itab. reflexivity. Qed.

End CXFEL.
