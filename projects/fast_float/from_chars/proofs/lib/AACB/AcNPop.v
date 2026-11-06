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
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.AcFixS.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint fa_cont (k : nat) (acc : tree bval) : tree bval :=
  match k with O => acc | Datatypes.S k' => fa_cont k' (tset (Pos.of_succ_nat k') (BK 250) acc) end.
Definition chunk_lin (a : ast) (c : Z) : lin := laddc (ladd (p_sb a) (lscale (sz_tbl c) (p_j a c))) (4294967296 * c).
Definition chsh_lin (a : ast) (c : Z) : lin := laddc (ladd (p_sh a) (lscale (sz_tbl c / 8) (p_j a c))) (536870912 * c).
Definition chunk_rgs (a : ast) (c : Z) : list region :=
  [RG (chunk_lin a c) (lconst (sz_tbl c)) RZ TEmpty;      (* [comment removed for export] *)
   RG (chsh_lin a c) (lconst (sz_tbl c / 8)) RW (fa_cont (Z.to_nat (sz_tbl c / 8)) TEmpty)].

(* [comment removed for export] *)
Fixpoint set_nth {A} (i : nat) (x : A) (l : list A) : list A :=
  match l, i with [], _ => [] | _ :: r, O => x :: r | y :: r, Datatypes.S i' => y :: set_nth i' x r end.
Definition pri_step (a : ast) (c : Z) : list lin :=
  set_nth (6 + 2 * cidx c) (lconst 262144) (set_nth (5 + 2 * cidx c) (laddc (p_j a c) 1) (a_pri a)).
Definition a_step (a : ast) (c : Z) : ast :=
  let pri := pri_step a c in
  let a0 := with_pri a (a_own a) pri in
  with_pri a (own_of (fst (a_dep a)) (snd (a_dep a)) ++ pri_own a0) pri.

(* [comment removed for export] *)
Definition FU_WORDS : list (Z * nat * Z) :=
  [(910448, 8%nat, 1532192); (1532192, 8%nat, 4096); (910464, 8%nat, 1540520); (1540664, 8%nat, 0); (1540780, 1%nat, 0);
   (929856, 4%nat, 4294967295); (929872, 1%nat, 0);
   (941788, 1%nat, 1); (910480, 8%nat, 943736); (943736, 8%nat, 2147450880); (910488, 8%nat, 947048); (947048, 8%nat, 0);
   (910496, 8%nat, 947056); (947056, 8%nat, 0); (910504, 8%nat, 947040); (947040, 8%nat, 140737488355327);
   (910512, 8%nat, 918480); (918480, 8%nat, 870660); (941792, 1%nat, 1)].
Definition fu_words_ok (G : list region) : bool := forallb (fun e => rdc IMGP G (fst (fst e)) (snd (fst e)) (snd e)) FU_WORDS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rg_has (G : list region) (a : lin) (n : Z) : bool :=
  existsb_l (fun R => match lin_off a (rg_base R), is_const (rg_size R) with Some o, Some z => Z.leb 0 o &&& Z.leb (o + n) z | _, _ => false end) G.
(* [comment removed for export] *)
Definition in_rg_const (G : list region) (lo hi : Z) : bool :=
  existsb_l (fun R => match is_const (rg_base R), is_const (rg_size R) with Some b, Some z => Z.leb b lo &&& Z.leb hi (b + z) | _, _ => false end) G.
Definition fu_tls_ok (S : sst) (gs : list (lin * lin * gkind)) (a : ast) : bool :=
  let G := s_rgs S in let TPl := rget (s_regs S) (rk 4) in
  match rdw IMGP G (lconst 941796) 4 with
  | Some Kl => match is_const Kl, is_const TPl with
    | Some K, Some TP => match rdw IMGP G (laddc TPl (-88)) 8 with
      | Some TSDAl => match is_const TSDAl with
        | Some TSDA => match rdw IMGP G (laddc TSDAl (8 * K)) 8 with
          | Some PTl => match rdw IMGP G (laddc PTl 152) 8 with
            | Some Tl => (Z.leb 0 K && Z.leb K 1023 && lin_eqb (laddc Tl 208) (p_ca a) && lin_eqb Tl (p_tg a) &&
                          Z.leb 65624 TP && Z.leb TP 6537216 && Z.leb 65536 TSDA && Z.leb (TSDA + 8 * K + 8) 6537216 &&
                          (* [comment removed for export] *)
                          rg_has G PTl 160 && existsb_l (fun g => lin_eqb (fst (fst g)) PTl &&& Z.leb 160 (gsz_lo (s_facts S) g)) gs)%bool
            | None => false end
          | None => false end
        | None => false end
      | None => false end
    | _, _ => false end
  | None => false end.

(* [comment removed for export] *)
Definition ENVC_RNG : list (Z * Z) :=
  [(910448, 910520); (918480, 918488); (929848, 929873); (941788, 941800); (943736, 943744); (947040, 947064);
   (1532192, 1532200); (1540664, 1540672); (1540780, 1540781)].
Definition envc_ok (G : list region) : bool := forallb (fun p => in_rg_const G (fst p) (snd p)) ENVC_RNG.

(* [comment removed for export] *)
Definition K34 : list positive := List.map rk [3; 4].
Fixpoint with_regs (S : sst) (l : list (Z * lin)) : sst := match l with [] => S | (r, x) :: l' => with_regs (with_reg S (rk r) x) l' end.
Definition ecall_tpl (L : sst) (W : list nat) (ad : lin) : sst :=
  with_regs (hand_post L 0x73c38 K34 W) [(10, ad); (11, lconst 262144); (12, lconst 3); (13, lconst 50); (14, lconst 18446744073709551615); (15, lconst 0); (17, lconst 222)].

(* [comment removed for export] *)
Definition sb_words_ok (G : list region) (a : ast) : bool :=
  match rdw IMGP G (lconst 929848) 8, rdw IMGP G (lconst 929864) 8 with
  | Some l1, Some l2 => lin_eqb l1 (p_sb a) &&& lin_eqb l2 (l_rip a)
  | _, _ => false
  end.

Definition np_front (S : sst) (n : positive) (rgs : list region) : sst := SST 0x44004 (s_regs S) rgs [] n RNone.
Definition np_rest (S : sst) (rgs : list region) : sst := SST 0x44004 (s_regs S) rgs (s_facts S) (s_next S) RNone.

Definition apost_npop0 (LIMIT : Z) (c : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let SPl := rget (s_regs S) (rk 2) in let fs := s_facts S in
  obool (a_on a && Nat.eqb (List.length (a_pri a)) PRI_LEN && existsb (Z.eqb c) CLS && Z.eqb (s_pc S) 0x44004 && rsv_none_b (s_resv S) &&
         list_eqb pair_eqb (sm_own M) (a_own a))%bool (
  obind (find_stk (s_rgs S) SPl) (fun stk =>
  obind (find_ro (s_rgs S)) (fun ro =>
  obind (find_rg_acc' (rg_is (laddc (p_tg a) 2872) 16 RW) (s_rgs S) O) (fun ist =>
  obind (nth_error (s_rgs S) stk) (fun R =>
  obind (lin_off SPl (rg_base R)) (fun o =>
  obind (carve_of S stk [o - 2048; o] [Datatypes.S stk; ro_split ro stk 2; ro_split ist stk 2]) (fun cv =>
  obind (find_grant (sm_maps M) (p_pg a) PG_SIZE) (fun jP =>
  obind (find_grant (sm_maps M) (p_tg a) TG_SIZE) (fun jT =>
  obind (nth_error (sm_maps M) jP) (fun gP =>
  let front := firstn 3 (carve_rgs cv) in let rest := skipn 3 (carve_rgs cv) in
  let L := np_front S (s_next S) front in
  let Sp := np_rest S rest in
  let lohi := irange fs SPl in let jr := irange fs (p_j a c) in let ndr := irange fs (rget (s_regs S) (rk 12)) in
  (* [comment removed for export] *)
  let L1 := ecall_tpl L [0%nat; 2%nat] (l_rb a c) in
  let L2 := ecall_tpl (fix_post L1 (l_rb a c)) [0%nat; 2%nat] (l_fa a c) in
  let Lb := np_front S (s_next S + 66) front in
  let X := with_reg (mrg (hand_post Lb 0x44224 KALLk [0%nat; 2%nat]) Sp) (rk 10) (chunk_lin a c) in
  let ixb := inv_ix (cv_ix cv) (length (cv_split cv)) in
  let a' := a_step a c in
  let M' := with_own M (a_own a') in
  (* [comment removed for export] *)
  obool (perm_ix_ok (length (cv_split cv)) (cv_ix cv) &&&
         lin_eqb (rget (s_regs S) (rk 10)) (lconst 929816) &&& lin_eqb (rget (s_regs S) (rk 11)) (p_ca a) &&& lin_eqb (rget (s_regs S) (rk 13)) (lconst 8) &&&
         Z.leb (sz_tbl (c - 1) + 1) (fst ndr) &&& Z.leb (snd ndr) (sz_tbl c) &&&   (* [comment removed for export] *)
         fact_implied fs (FMod SPl 4 0) &&& Z.leb (2^46 + 8192) (fst lohi) &&& Z.leb (snd lohi) (2^47) &&&
         rg_hdr_b (nth_error front 0) (laddc SPl (-2048)) (lconst 2048) RW &&& ro_b (nth_error front 1) &&&
         rg_hdr_b (nth_error front 2) (laddc (p_tg a) 2872) (lconst 16) RW &&&
         sb_words_ok (s_rgs S) a &&&
         Z.leb (snd jr + mc_tbl c / 2 + 1) (262144 / sz_tbl c) &&&
         gkind_eqb (snd gP) GE &&& band_ok (s_facts S) M SPl &&&   (* [comment removed for export] *)
         state_wf L &&&
         perm_ix_ok (length (s_rgs X)) ixb &&& forallb (lwf (s_next S)) (a_pri a') &&&
         forallb (fun p => lwf (s_next S) (fst p) &&& lwf (s_next S) (snd p)) (a_own a') &&&
         forallb_l (pri_sep_c fs (sm_maps M) ASEGSR jP jT (sm_sp M) a) (s_rgs (mrg L Sp)) &&&
         (if Z.ltb 0 (fst jr) then true    (* [comment removed for export] *)
          else (fu_words_ok (s_rgs S) &&& fu_tls_ok Sp (sm_maps M) a &&& envc_ok (s_rgs Sp) &&&
                fixkeep_ok_s LIMIT ASEGSR (mrg L1 Sp) M 262144 false jP GE &&&
                fixkeep_ok_s LIMIT ASEGSR (mrg L2 Sp) M 262144 false jP GE))) (
  obind (steps_rgs (s_next X) (s_facts X) (List.map (fun t => nth t (s_rgs X) (RG lc0 lc0 RW TEmpty)) ixb) (List.repeat (RMergeCC stk) 2)) (fun l'' =>
  Some (with_rgs X (chunk_rgs a c ++ l''), M', a'))))))))))))).
(* [comment removed for export] *)
Definition apost_npop (LIMIT : Z) (c : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  apost_npop0 LIMIT c (with_facts S (s_facts S ++ [sp_fact M])) M a.

(* [comment removed for export] *)
Definition shp_rg (a : ast) (c : Z) : region :=
  RG (chsh_lin a c) (lconst (sz_tbl c / 8)) RW (fa_cont (Z.to_nat (sz_tbl c / 8)) TEmpty).
Definition apost_shb (c : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let fs := s_facts S in let jr := irange fs (p_j a c) in
  obool (a_on a && Nat.eqb (List.length (a_pri a)) PRI_LEN && existsb (Z.eqb c) CLS && list_eqb pair_eqb (sm_own M) (a_own a))%bool (
  obind (find_grant (sm_maps M) (p_pg a) PG_SIZE) (fun jP =>
  obind (find_grant (sm_maps M) (p_tg a) TG_SIZE) (fun jT =>
  obool (Z.leb 1 (fst jr) && Z.leb (snd jr + 1) (262144 / sz_tbl c) &&
         forallb_l (pri_sep_c fs (sm_maps M) ASEGSR jP jT (sm_sp M) a) (s_rgs S))%bool
    (Some (with_rgs S (shp_rg a c :: s_rgs S), M, a))))).
Fixpoint find_rg_eq (R : region) (l : list region) (i : nat) : option nat :=
  match l with [] => None | R' :: r => if rg_eqb R' R then Some i else find_rg_eq R r (Datatypes.S i) end.
Definition apost_shg (c : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (a_on a && Nat.eqb (List.length (a_pri a)) PRI_LEN && existsb (Z.eqb c) CLS && list_eqb pair_eqb (sm_own M) (a_own a) &&
         Z.leb 1 (fst (irange (s_facts S) (p_j a c))))%bool (
  obind (find_rg_eq (shp_rg a c) (s_rgs S) O) (fun i =>
  Some (with_rgs S (remove_nth i (s_rgs S)), M, a))).

(* [comment removed for export] *)
Fixpoint incr_b (l : list nat) : bool := match l with x :: ((y :: _) as r) => (Nat.ltb x y && incr_b r)%bool | _ => true end.
Fixpoint remove_ixs {A} (ix : list nat) (l : list A) : list A :=   (* [comment removed for export] *)
  match ix with [] => l | i :: r => remove_nth i (remove_ixs r l) end.
Definition give_hdr_ok (M : smodel) (a : ast) (c : Z) (S : sst) : bool :=
  (a_on a && Nat.eqb (List.length (a_pri a)) PRI_LEN && existsb (Z.eqb c) CLS && list_eqb pair_eqb (sm_own M) (a_own a) &&
   Z.leb 1 (fst (irange (s_facts S) (p_j a c))))%bool.
Definition apost_give (c : Z) (ix : list nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (give_hdr_ok M a c S && incr_b ix &&
         forallb (fun i => match nth_error (s_rgs S) i with Some R => live_in (s_facts S) a R c | None => false end) ix)%bool
    (Some (with_rgs S (remove_ixs ix (s_rgs S)), M, a)).
(* [comment removed for export] *)
Definition apost_shrink (c : Z) (i : nat) (s : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obind (nth_error (s_rgs S) i) (fun R =>
  obool (give_hdr_ok M a c S && Z.leb 1 s && Z.leb s (fst (irange (s_facts S) (rg_size R))) && live_in (s_facts S) a R c)%bool
    (Some (with_rgs S (firstn i (s_rgs S) ++ RG (rg_base R) (lconst s) (rg_kind R) (sub_cont (rg_cont R) 0 s) :: skipn (Datatypes.S i) (s_rgs S)), M, a))).
(* [comment removed for export] *)
