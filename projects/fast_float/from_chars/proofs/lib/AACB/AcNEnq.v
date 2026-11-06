(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen AcAst AcHA AcFacts AcCarveP AcMALlib AcPutN AcTbl AcConv AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNPop.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.AcFixS OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition QCLS : Z := 24.
(* [comment removed for export] *)
Definition batch_lin (a : ast) (qj : lin) : lin := laddc (ladd (p_sb a) (lscale 8192 qj)) (4294967296 * QCLS).

(* [comment removed for export] *)
Definition q_step_room (a : ast) (sz : lin) : list lin :=
  set_nth 67 (ladd (p_qb a) sz) (set_nth 66 (laddc (p_qn a) 1) (a_pri a)).
Definition q_step_new (a : ast) (sz : lin) : list lin :=
  set_nth 67 (laddc sz 8192) (set_nth 66 (lconst 1) (set_nth 65 (p_j a QCLS) (pri_step a QCLS))).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition q_step_drain (pri : list lin) (a : ast) (qjl qbl : lin) : list lin :=
  set_nth 70 (ladd (p_gb a) qbl) (set_nth 69 qjl (set_nth 68 (laddc (p_gn a) 1) (set_nth 67 (lconst 0) (set_nth 66 (lconst 0) pri)))).
Definition KT2k : list positive := List.map rk [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition a_qstep (a : ast) (pri : list lin) : ast :=
  let a0 := with_pri a (a_own a) pri in
  with_pri a (own_of (fst (a_dep a)) (snd (a_dep a)) ++ pri_own a0) pri.

(* [comment removed for export] *)
Definition batch_sep_at (fs : list fact) (a : ast) (ql : lin) (R : region) : bool :=
  if live_in fs a R QCLS then
    (if sep_cached a R then true
     else let qr := irange fs ql in let zhi := snd (irange fs (rg_size R)) in
          match lin_off (rg_base R) (l_rb a QCLS) with
          | Some d => if Z.leb (d + zhi) (8192 * fst qr) then true else Z.leb (8192 * (snd qr + 1)) d
          | None => match lin_off (ladd (rg_base R) (rg_size R)) (l_rb a QCLS) with
                    | Some e => if Z.leb e (8192 * fst qr) then true else Z.leb (8192 * (snd qr + 1)) (e - zhi)
                    | None => true     (* [comment removed for export] *)
                    end
          end)
  else true.
Definition batch_sep (fs : list fact) (a : ast) (R : region) : bool := batch_sep_at fs a (p_qj a) R.

Definition nq_front (S : sst) (n : positive) (rgs : list region) : sst := SST 0x43e20 (s_regs S) rgs [] n RNone.
Definition nq_rest (S : sst) (rgs : list region) : sst := SST 0x43e20 (s_regs S) rgs (s_facts S) (s_next S) RNone.

Definition apost_nenq0 (LIMIT : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let SPl := rget (s_regs S) (rk 2) in let fs := s_facts S in
  obool (a_on a &&& Nat.eqb (List.length (a_pri a)) PRI_LEN &&& Z.eqb (s_pc S) 0x43e20 &&& rsv_none_b (s_resv S) &&&
         list_eqb pair_eqb (sm_own M) (a_own a)) (
  obind (find_stk (s_rgs S) SPl) (fun stk =>
  obind (find_ro (s_rgs S)) (fun ro =>
  obind (find_rg_acc' (rg_is (laddc (p_tg a) 2872) 16 RW) (s_rgs S) O) (fun ist =>
  obind (nth_error (s_rgs S) stk) (fun R =>
  obind (lin_off SPl (rg_base R)) (fun o =>
  obind (carve_of S stk [o - 2064; o] [Datatypes.S stk; ro_split ro stk 2; ro_split ist stk 2]) (fun cv =>
  obind (find_grant (sm_maps M) (p_pg a) PG_SIZE) (fun jP =>
  obind (find_grant (sm_maps M) (p_tg a) TG_SIZE) (fun jT =>
  obind (nth_error (sm_maps M) jP) (fun gP =>
  let front := firstn 3 (carve_rgs cv) in let rest := skipn 3 (carve_rgs cv) in
  let L := nq_front S (s_next S) front in
  let Sp := nq_rest S rest in
  let lohi := irange fs SPl in
  let szl := rget (s_regs S) (rk 14) in
  let qnr := irange fs (p_qn a) in let qbr := irange fs (p_qb a) in let szr := irange fs szl in
  let s6r := irange fs (rget (s_regs S) (rk 22)) in let jr := irange fs (p_j a QCLS) in
  let room := Z.leb 1 (fst qnr) in
  let gnr := irange fs (p_gn a) in let gbr := irange fs (p_gb a) in
  let qbl' := if room then ladd (p_qb a) szl else laddc szl 8192 in     (* [comment removed for export] *)
  (* [comment removed for export] *)
  let qbf := irange fs qbl' in
  let qblo := Z.max (fst qbr + fst szr + (if room then 0 else 8192)) (fst qbf) in
  let qbhi := Z.min (snd qbr + snd szr + (if room then 0 else 8192)) (snd qbf) in
  let nodrain := Z.leb qbhi (fst s6r) in
  let pri0 := if room then q_step_room a szl else q_step_new a szl in
  let pri' := if nodrain then pri0 else q_step_drain pri0 a (if room then p_qj a else p_j a QCLS) qbl' in
  let a' := a_qstep a pri' in
  let M' := with_own M (a_own a') in
  (* [comment removed for export] *)
  let L1 := ecall_tpl L [0%nat; 2%nat] (l_rb a QCLS) in
  let L2 := ecall_tpl (fix_post L1 (l_rb a QCLS)) [0%nat; 2%nat] (l_fa a QCLS) in
  let Lb := nq_front S (s_next S + 66) front in
  let X := if nodrain then mrg (hand_post Lb 0x43d4c KALLk [0%nat; 2%nat]) Sp
           else with_reg (mrg (hand_post Lb 0x43d4c KT2k [0%nat; 2%nat]) Sp) (rk 1) (lconst 0x43d4c) in
  let ixb := inv_ix (cv_ix cv) (length (cv_split cv)) in
  obool (perm_ix_ok (length (cv_split cv)) (cv_ix cv) &&&
         lin_eqb (rget (s_regs S) (rk 10)) (l_cb a) &&& lin_eqb (rget (s_regs S) (rk 11)) (p_ca a) &&&
         lin_eqb (rget (s_regs S) (rk 9)) (l_cb a) &&& lin_eqb (rget (s_regs S) (rk 1)) (lconst 0x43e14) &&&
         fact_implied fs (FMod SPl 4 0) &&& Z.leb (2^46 + 8192) (fst lohi) &&& Z.leb (snd lohi) (2^47) &&&
         rg_hdr_b (nth_error front 0) (laddc SPl (-2064)) (lconst 2064) RW &&& ro_b (nth_error front 1) &&&   (* [comment removed for export] *)
         rg_hdr_b (nth_error front 2) (laddc (p_tg a) 2872) (lconst 16) RW &&&
         sb_words_ok (s_rgs S) a &&&
         (* [comment removed for export] *)
         (if room then Z.leb (snd qnr) 1020 &&& Z.leb 0 (fst (irange fs (p_qj a))) &&& Z.leb (snd (irange fs (p_qj a))) 31
          else Z.eqb (snd qnr) 0 &&& Z.eqb (snd qbr) 0 &&& Z.leb (snd jr + mc_tbl QCLS / 2 + 1) (262144 / sz_tbl QCLS)) &&&
         (* [comment removed for export] *)
         Z.leb (snd s6r) (2^40) &&& Z.leb (snd szr) (2^40) &&&
         (if nodrain then true
          else Z.leb (snd s6r + 1) qblo &&&                                            (* [comment removed for export] *)
               lin_eqb (rget (s_regs S) (rk 8)) (lconst 930544) &&&                    (* [comment removed for export] *)
               match is_const (rg_size R) with Some zz => Z.leb (o + 16) zz | None => false end &&&   (* [comment removed for export] *)
               match rdw IMGP (s_rgs S) (lconst 930608) 8 with                         (* [comment removed for export] *)
               | Some mxl => match is_const mxl with Some mxs => Z.leb (qbhi + snd gbr) mxs &&& Z.ltb mxs (2^62) | None => false end
               | None => false end &&&
               (Z.eqb (snd gnr) 0 ||| (Z.leb 1 (fst gnr) &&& Z.leb 0 (fst (irange fs (p_gl a))) &&& Z.leb (snd (irange fs (p_gl a))) 31)) &&&
               Z.leb (snd gnr) 4294967294 &&&
               (if room then true else Z.ltb 0 (fst jr))) &&&                            (* [comment removed for export] *)
         gkind_eqb (snd gP) GE &&& band_ok (s_facts S) M SPl &&&
         state_wf L &&&
         perm_ix_ok (length (s_rgs X)) ixb &&& forallb (lwf (s_next S)) (a_pri a') &&&
         forallb (fun p => lwf (s_next S) (fst p) &&& lwf (s_next S) (snd p)) (a_own a') &&&
         forallb_l (fun R => pri_sep_c fs (sm_maps M) ASEGSR jP jT (sm_sp M) a R &&& (if room then batch_sep fs a R else true) &&&
                             (* [comment removed for export] *)
                             (if nodrain then true else if Z.eqb (snd gnr) 0 then true else batch_sep_at fs a (p_gl a) R)) (s_rgs (mrg L Sp)) &&&
         (if room then true
          else if Z.ltb 0 (fst jr) then true    (* [comment removed for export] *)
          else (fu_words_ok (s_rgs S) &&& fu_tls_ok Sp (sm_maps M) a &&& envc_ok (s_rgs Sp) &&&
                fixkeep_ok_s LIMIT ASEGSR (mrg L1 Sp) M 262144 false jP GE &&&
                fixkeep_ok_s LIMIT ASEGSR (mrg L2 Sp) M 262144 false jP GE))) (
  obind (steps_rgs (s_next X) (s_facts X) (List.map (fun t => nth t (s_rgs X) (RG lc0 lc0 RW TEmpty)) ixb) (List.repeat (RMergeCC stk) 2)) (fun l'' =>
  Some (with_rgs X l'', M', a'))))))))))))).
(* [comment removed for export] *)
Definition apost_nenq (LIMIT : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  apost_nenq0 LIMIT (with_facts S (s_facts S ++ [sp_fact M])) M a.
(* [comment removed for export] *)
