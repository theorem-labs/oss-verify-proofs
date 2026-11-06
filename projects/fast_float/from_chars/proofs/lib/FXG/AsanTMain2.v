(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSubst FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen FxChain FxWvC FxChMain FxChEntM.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChRecont.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChAllow OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChRecont.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTbl AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.

Module AsanStartCert.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma startup_ok_all : (startup_ok_c 176 4080 5 && startup_ok_c 4096 4176 67 && startup_ok_c 4192 4256 68)%bool = true.
Proof. exact startup_ok_res. Qed.
Lemma startup_ok_C : startup_ok_c 176 4080 5 = true.
Proof. pose proof startup_ok_all as H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. exact H. Qed.
Lemma startup_ok_A : startup_ok_c 4096 4176 67 = true.
Proof. pose proof startup_ok_all as H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. exact H. Qed.
Lemma startup_ok_B : startup_ok_c 4192 4256 68 = true.
Proof. pose proof startup_ok_all as H. apply andb_prop in H as [_ H]. exact H. Qed.
End AsanStartCert.

Module AsanStartAll.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanStartCert.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition FINALS_ALL : list (sst * smodel) := FINALS_c 176 4080 5 ++ FINALS_c 4096 4176 67 ++ FINALS_c 4192 4256 68.

Section All.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Variables (sp brk0 mb : word) (draw : EntryDraw) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ASEGS brk0.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hid : valid_id (in_uid inp).

#[using="Hoff Hsp Hbrk Hfit Hva Hve Hid"] Theorem asan_startup : forall T,
  (forall S' M' E' ms' model', In (S', M') FINALS_ALL ->
     DEN ASEGS LIM (model0 sp brk0 mb LIM inp) (m0 sp draw inp) E' S' M' ms' model' ->
     realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (init_config ASEGS Asan.M.init_pc APH sp brk0 mb draw LIM inp) T.
Proof. LiaFast.lf_pins (fun (Hoff Hsp Hbrk Hfit Hva Hve Hid : LiaFast.U) => LiaFast.u0).
  intros T Hk. pose proof (ofs_b sp inp Hsp Hfit Hva Hve) as (O1 & O2 & O3 & O4 & O5).
  unfold FINALS_ALL in Hk.
  assert (Hq : OFS sp = 16 * (OFS sp / 16)) by (pose proof (Z.div_mod (OFS sp) 16 ltac:(lia)); lia).
  destruct (Z_le_gt_dec (OFS sp) 4080) as [Hc|Hc]; [|destruct (Z_le_gt_dec (OFS sp) 4176) as [Hc'|Hc']].
  - apply (asan_startup_cls cfg Hoff sp brk0 mb draw inp Hsp Hbrk Hfit Hva Hve Hid 176 4080 5 ltac:(clear - O4 Hc; lia) ltac:(clear; lia)
             startup_ok_C T).
    intros S' M' E' ms' model' Hin Hd. apply (Hk S' M' E' ms' model'); [|exact Hd]. apply in_or_app. left. exact Hin.
  - apply (asan_startup_cls cfg Hoff sp brk0 mb draw inp Hsp Hbrk Hfit Hva Hve Hid 4096 4176 67 ltac:(clear - O4 Hc Hc' Hq; lia) ltac:(clear; lia)
             startup_ok_A T).
    intros S' M' E' ms' model' Hin Hd. apply (Hk S' M' E' ms' model'); [|exact Hd]. apply in_or_app. right. apply in_or_app. left. exact Hin.
  - apply (asan_startup_cls cfg Hoff sp brk0 mb draw inp Hsp Hbrk Hfit Hva Hve Hid 4192 4256 68 ltac:(clear - O4 Hc Hc' Hq; lia) ltac:(clear; lia)
             startup_ok_B T).
    intros S' M' E' ms' model' Hin Hd. apply (Hk S' M' E' ms' model'); [|exact Hd]. apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.
End All.
End AsanStartAll.


Module AsanFinAB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTbl AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require Export AsanFinC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanStartAll.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma finals_all_eq : FINALS_ALL = FINC ++ FINA ++ FINB.
Proof. exact finals_res_eq. Qed.
End AsanFinAB.


Module AsanFinEnt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSubst FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTbl AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition S1x : sst := fst (List.nth 0 FINC (S0c 176 4080 5, M0)).
Definition M1x : smodel := snd (List.nth 0 FINC (S0c 176 4080 5, M0)).
(* [comment removed for export] *)
Fixpoint bind_terms (tp ts : list (positive * Z)) (σ : tree lin) : tree lin :=
  match tp, ts with
  | (x, k) :: tp', (y, k') :: ts' => if Z.eqb k k' then bind_terms tp' ts' (match tget x σ with Some _ => σ | None => tset x (lvar y) σ end) else σ
  | _, _ => σ
  end.
Definition bind_shape (lp ls : lin) (σ : tree lin) : tree lin :=
  if Nat.eqb (List.length (l_t lp)) (List.length (l_t ls)) then bind_terms (l_t lp) (l_t ls) σ else σ.
Fixpoint bind_shapes (ps : list (lin * lin)) (σ : tree lin) : tree lin :=
  match ps with [] => σ | (lp, ls) :: r => bind_shapes r (bind_shape lp ls σ) end.
Fixpoint tfold_acc {A B} (f : positive -> A -> B -> B) (t : tree A) (k : positive -> positive) (acc : B) : B :=
  match t with
  | TEmpty => acc
  | TNode l v r => let acc1 := match v with Some x => f (k xH) x acc | None => acc end in
                   tfold_acc f r (fun p => k (xI p)) (tfold_acc f l (fun p => k (xO p)) acc1)
  end.
Definition bv_pairs (tp ts : tree bval) : list (lin * lin) :=
  tfold_acc (fun k v acc => match v, tget k ts with BV l _, Some (BV l' _) => (l, l') :: acc | _, _ => acc end) tp (fun p => p) [].
Definition pairs_st (F P : sst) (MF MP : smodel) : list (lin * lin) :=
  List.map (fun k => (rget (s_regs P) (Pos.of_succ_nat k), rget (s_regs F) (Pos.of_succ_nat k))) (List.seq 1 31) ++
  List.concat (List.map (fun '(R, R') => (rg_base R', rg_base R) :: (rg_size R', rg_size R) :: bv_pairs (rg_cont R') (rg_cont R)) (List.combine (s_rgs F) (s_rgs P))) ++
  List.map (fun '(g, g') => (fst (fst g'), fst (fst g))) (List.combine (sm_maps MF) (sm_maps MP)) ++
  List.map (fun '(g, g') => (fst g', fst g)) (List.combine (sm_allow MF) (sm_allow MP)) ++
  [(sm_sp MP, sm_sp MF); (sm_brk MP, sm_brk MF); (sm_sbrk MP, sm_sbrk MF)].
Fixpoint bind_bares (ps : list (lin * lin)) (σ : tree lin) : tree lin :=
  match ps with [] => σ | (lp, ls) :: r => bind_bares r (bind_bare lp ls σ) end.
Definition match_shape (F P : sst) (MF MP : smodel) : tree lin := let ps := pairs_st F P MF MP in bind_shapes ps (bind_bares ps TEmpty).
End AsanFinEnt.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanStartAll OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanFinAB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanFinEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcConvG AcSubst.
Import ListNotations.

Module AsanShort.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition F3000 : nat := 3000.
Definition F5000 : nat := 5000.
Definition F8000 : nat := 8000.
Definition F30000 : nat := 30000.
(* [comment removed for export] *)
Definition apost0 (nk : Empty_set) (S : sst) (M : smodel) (a : unit) : option (sst * smodel * unit) := match nk with end.
Definition anil0 (a : unit) : bool := true.
Definition aeqb0 (a b : unit) : bool := true.
Definition awf0 (n : positive) (a : unit) : bool := true.
Definition HA0 (E : valu) (M : smodel) (a : unit) (m0 : word -> option byte) : Prop := True.
Definition acopy0 (a : unit) : list srec := [].
Definition MC : Type := @mchain Empty_set.

(* [comment removed for export] *)
Definition F0 : sst * smodel := List.nth 0 FINC (S0c 176 4080 5, M0).
Definition S1 : sst := fst F0.
Definition M1 : smodel := snd F0.
Definition PV : lin := lvar 8.
Definition MSG : list Z := [99;108;105;58;32;105;110;112;117;116;32;115;104;111;114;116;101;114;32;116;104;97;110;32;104;101;97;100;101;114;10].
Definition SH : shp := ShAlt2 (ShEmit [] 2) (ShEmit [PD 2 (SLit MSG) (lconst 0)] 2).

(* [comment removed for export] *)
Definition IB : nat := Eval vm_compute in (rg_index (s_rgs S1) 0x607400 O + 4)%nat.   (* [comment removed for export] *)
Definition P_OPEN : plan := PJoin F3000 [0x8fc60] 0xd3954 PFin [].
Definition P_MALLOC : plan := PJoin F5000 [0x8fd58] 0x73c44 PFin [].
Definition P_TO_MMAP : plan := PJoin F5000 [] 0x73c44 PFin [].
Definition P_TO_READ : plan := PJoin F8000 [] 0xd3954 PFin [].
Definition P_R2 : plan := PJoin F8000 [0xd3954] 0x8fb48 (PJoin F8000 [] 0xd3954 PFin []) [].
Definition P_R3 : plan := PJoin F8000 [] 0xd3954 PFin [].
Definition P_WV : plan := PJoin F8000 [] 0xca390 PFin [].
Fixpoint jplanW (k : nat) : plan := match k with
  | O => PRun F30000 [0x73c44; 0xca418] []
  | Datatypes.S k' => let p := jplanW k' in PJoin F30000 [0x73c44; 0xca418; 0x73458; 0x7348c] 0x632dc p
       [(0x73458, PLoopW 200 [0x73464] [(0x73464, p)]); (0x7348c, PLoopW 200 [0x7349c] [(0x7349c, p)])] end.
Fixpoint jplan2 (k : nat) : plan := match k with
  | O => PRun F30000 [0x73c44; 0xc4798] []
  | Datatypes.S k' => let p := jplan2 k' in PJoin F30000 [0x73c44; 0xc4798; 0x73458; 0x7348c; 0xd3160] 0x632dc p
       [(0x73458, PLoopW 200 [0x73464] [(0x73464, p)]); (0x7348c, PLoopW 200 [0x7349c] [(0x7349c, p)]);
        (0xd3160, PLoopW 200 [0xd317c] [(0xd317c, p)])] end.
Definition KFX : MC := MChain (CNode (NFixNew 0x40000 12) CEnd) (MSegK 40 (jplan2 8) (KCons 0x73c44 222
   (MChain (CNode (NFixNew 0x40000 12) CEnd) (MSegK 40 (jplan2 8) (KCons 0xc4798 94 MExit KNil))) KNil)).
(* [comment removed for export] *)
Definition P_RETRY : plan := PRun F3000 [0xca418; 0xca39c] [].
Definition KAFTER : MC := MSegK 40 (jplanW 10) (KCons 0x73c44 222 KFX KNil).
Definition WB : MC := MWritev 0x21087 (MSegK 20 P_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))).
Definition KW : MC := MJoin (MWritev 0x21087 (MSegK 20 P_RETRY (KCons 0xca418 66 (MLoopW 22 WB (KCons 0xca39c 0 (MPop MEnd) KNil)) (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c KAFTER.
Definition KCL : MC := MSegK 20 P_WV (KCons 0xca390 66 KW KNil).
(* [comment removed for export] *)
Definition KJ : MC := MSegK 20 P_R2 (KCons 0xd3954 63 (MRead IB 0x10 (MSegK 20 P_R3 (KCons 0xd3954 57 MEnd KNil)) MEnd) (KCons 0xd3954 57 MEnd KNil)).
Definition KOK : MC :=
  MSegK 20 P_MALLOC (KCons 0x73c44 222
    (MChain (CNode (NNull 0x12000 GE true true false) (COp (TSepW 0 12) CEnd))
      (MSegK 20 P_TO_MMAP (KCons 0x73c44 222
         (MChain (CNode (NFixNew 0x20000 11) CEnd)
           (MSegK 20 P_TO_READ (KCons 0xd3954 63 (MJoin (MRead IB 0x10 KJ MEnd) 0xd3954 (MClose KCL)) (KCons 0x3febc 0 MVoid KNil)))) (KCons 0x44360 0 MVoid KNil))))
    (KCons 0x8fd58 0 MEnd KNil)).
Definition SHORT : MC := MSegK 20 P_OPEN (KCons 0xd3954 56 (MOpen MEnd KOK) (KCons 0x8fc60 0 MEnd KNil)).

(* [comment removed for export] *)
Definition short_res : option (list (sst * smodel * fstate * shp * unit)) :=
  mcheck ASEGS LIM TBLd IMGd PV 0 5 false None apost0 anil0 aeqb0 awf0 acopy0 asub_id agok_t alins_nil aset_id amod_t [] [] SHORT S1 M1 FSClosed SH tt.
Definition is_some {X} (o : option X) : bool := match o with Some _ => true | None => false end.
Definition short_chk : bool := is_some short_res.
End AsanShort.

Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition sep4 (S : sst) (M : smodel) : sst :=
  List.fold_left (fun S j => if Nat.eqb j 4 then S else match sepw_post S M 4 j with Some S' => S' | None => S end) (List.seq 0 (List.length (sm_maps M))) S.
(* [comment removed for export] *)
Definition IBSS : nat := Eval vm_compute in
  match FINC with F :: _ => match apost_convG (fst F) (snd F) ast0 with Some (S', _, _) => rg_index (s_rgs S') 0x617410 O | None => O end | [] => O end.
Definition NALW : nat := Eval vm_compute in List.fold_left (fun m F => Nat.min m (List.length (sm_allow (snd F)))) (FINC ++ FINA ++ FINB) 1000%nat.
(* [comment removed for export] *)
Definition conv1 (F : sst * smodel) : option (sst * smodel * ast) :=
  match apost_convG (fst F) (snd F) ast0 with
  | Some (S', M', a') =>
      let S1 := sep4 S' M' in
      if Nat.eqb (List.length (sm_allow M')) NALW then
        (* [comment removed for export] *)
        match List.nth_error (sm_maps M') 4, rz_track_post S1 IBSS 134833 with
        | Some g, Some S2 => match recont_post S2 IBSS 134833 0 with
                             | Some S3 => Some (S3, allow_ins M' 5 (laddc (fst (fst g)) 4096, 4096), a')
                             | None => None end
        | _, _ => None
        end
      else
        (* [comment removed for export] *)
        match recont_post S1 IBSS 135705 18446744073709551615 with
        | Some S2 => match recont_post S2 IBSS 134833 1 with Some S3 => Some (S3, M', a') | None => None end
        | None => None
        end
  | None => None
  end.
Definition CONV : list (sst * smodel * ast) := List.fold_right (fun F acc => match conv1 F with Some x => x :: acc | None => acc end) [] (FINC ++ FINA ++ FINB).
Definition FIN6 : list (sst * smodel) := List.map (fun '(St, Mx, _) => (St, Mx)) CONV.
Definition C0 : sst * smodel * ast := List.nth 0 CONV (S1x, M1x, ast0).
Definition T0 : sst := let '(St, _, _) := C0 in St.
Definition MT0 : smodel := let '(_, Mx, _) := C0 in Mx.
Definition AT0 : ast := let '(_, _, a) := C0 in a.
Definition sig (F : sst * smodel) (T : sst) (MT : smodel) : tree lin := match_shape (fst F) T (snd F) MT.
(* [comment removed for export] *)
Definition link_base (MT : smodel) (Fs : list (sst * smodel * tree lin * region)) (R : region) : option lin :=
  List.find (fun l => forallb (fun '(_, MF, σ, RF) => lin_eqb (rg_base RF) (lsubst σ l)) Fs)
    (List.concat (List.map (fun '(j, g) => match is_bare (fst (fst g)) with
                              | Some x => match Fs with
                                          | (_, MF0, _, RF0) :: _ => match List.nth_error (sm_maps MF0) j with
                                                                     | Some g0 => match is_const (lsub (rg_base RF0) (fst (fst g0))) with Some c => [laddc (lvar x) c] | None => [] end
                                                                     | None => [] end
                                          | [] => [] end
                              | None => [] end) (List.combine (List.seq 0 (List.length (sm_maps MT))) (sm_maps MT)))).
(* [comment removed for export] *)
Definition gcands (MT : smodel) (M0 : smodel) (l : lin) : list lin :=
  List.concat (List.map (fun '(g, g0) => match is_bare (fst (fst g)) with
                               | Some x => match is_const (lsub l (fst (fst g0))) with Some c => [laddc (lvar x) c] | None => [] end
                               | None => [] end) (List.combine (sm_maps MT) (sm_maps M0))).
Definition bmatch (Fs : list (sst * smodel * tree lin * region)) (k : positive) (v : bval) : bool :=
  forallb (fun '(_, _, σ, RF) => match tget k (rg_cont RF) with Some v' => bval_eqb v' (bsubst σ v) | None => false end) Fs.
Definition gen_cont0 (MT M0 : smodel) (Fs : list (sst * smodel * tree lin * region)) (t : tree bval) : tree bval * list positive :=
  tfold_acc (fun k v '(acc, bad) =>
      if bmatch Fs k v then (tset k v acc, bad) else
      match v with
      | BV l j => match List.find (fun l' => bmatch Fs k (BV l' j)) (gcands MT M0 l) with
                  | Some l' => (tset k (BV l' j) acc, bad)
                  | None => (acc, k :: bad) end
      | BK _ => (acc, k :: bad)
      end) t (fun p => p) (TEmpty, []).
(* [comment removed for export] *)
Definition wkey (k : positive) (j : Z) : positive := Pos.of_nat (Pos.to_nat k - Z.to_nat j).
Definition word_ok (Fs : list (sst * smodel * tree lin * region)) (k : positive) (j : Z) : bool :=
  forallb (fun '(_, _, _, RF) => match tget k (rg_cont RF) with Some (BV _ j') => Z.eqb j j' | _ => false end) Fs.
Fixpoint assoc_var (ws : list positive) (w : positive) (f : positive) : option positive :=
  match ws with [] => None | w' :: r => if Pos.eqb w w' then Some f else assoc_var r w (Pos.succ f) end.
Definition gen_cont (MT M0 : smodel) (Fs : list (sst * smodel * tree lin * region)) (t : tree bval) (fresh : positive) : tree bval * positive :=
  let '(acc, bad) := gen_cont0 MT M0 Fs t in
  let good := List.filter (fun k => match tget k t with Some (BV _ j) => word_ok Fs k j | _ => false end) bad in
  let ws := List.fold_left (fun ws k => match tget k t with
                                       | Some (BV _ j) => let w := wkey k j in if existsb (Pos.eqb w) ws then ws else ws ++ [w]
                                       | _ => ws end) good [] in
  (List.fold_left (fun acc k => match tget k t with
                                | Some (BV _ j) => match assoc_var ws (wkey k j) fresh with Some f => tset k (BV (lvar f) j) acc | None => acc end
                                | _ => acc end) good acc,
   Pos.of_nat (Pos.to_nat fresh + List.length ws)).
Definition gen_rg (MT : smodel) (Fs : list (sst * smodel * tree lin * region)) (R : region) (fresh : positive) : region * positive :=
  let base_ok := forallb (fun '(_, _, σ, RF) => lin_eqb (rg_base RF) (lsubst σ (rg_base R))) Fs in
  let '(c, fresh1) := gen_cont MT MT0 Fs (rg_cont R) fresh in
  (* [comment removed for export] *)
  let is_win := match is_const (rg_size R) with Some 8388608 => lin_eqb (rg_base R) (laddc SP (-8388608)) | _ => false end in
  let kd := if is_win then RW else
            if forallb (fun '(_, _, σ, RF) => rz_extra_ok RF (RG (rg_base R) (rg_size R) (rg_kind R) c)) Fs then rg_kind R else RW in
  if base_ok then (RG (rg_base R) (rg_size R) kd c, fresh1) else
  match link_base MT Fs R with
  | Some l => (RG l (rg_size R) kd c, fresh1)
  | None => (RG (lvar fresh1) (rg_size R) kd c, Pos.succ fresh1)
  end.
Fixpoint gen_rgs (MT : smodel) (Fs : list (sst * smodel * tree lin)) (rs : list region) (i : nat) (fresh : positive) : list region * positive :=
  match rs with
  | [] => ([], fresh)
  | R :: rs' => let '(R', f') := gen_rg MT (List.map (fun '(F, MF, σ) => (F, MF, σ, List.nth i (s_rgs F) R)) Fs) R fresh in
                let '(rs'', f'') := gen_rgs MT Fs rs' (Datatypes.S i) f' in (R' :: rs'', f'')
  end.
Definition refine (T : sst) (MT : smodel) : sst :=
  let Fs := List.map (fun F => (fst F, snd F, sig F T MT)) FIN6 in
  let '(rgs', fresh) := gen_rgs MT Fs (s_rgs T) O (s_next T) in
  let fs' := List.filter (fun f => forallb (fun '(F, _, σ) => fact_implied (s_facts F) (fsubst σ f)) Fs) (s_facts T) in
  SST (s_pc T) (s_regs T) rgs' fs' fresh (s_resv T).
Fixpoint gen_maps (Fs : list (sst * smodel * tree lin)) (gs : list (lin * lin * gkind)) (i : nat) (fresh : positive) : list (lin * lin * gkind) * positive :=
  match gs with
  | [] => ([], fresh)
  | g :: gs' => let ok := forallb (fun '(_, MF, σ) => match List.nth_error (sm_maps MF) i with Some g' => lin_eqb (fst (fst g')) (lsubst σ (fst (fst g))) | None => false end) Fs in
                let '(g1, f1) := if ok then (g, fresh) else ((lvar fresh, snd (fst g), snd g), Pos.succ fresh) in
                let '(r, f2) := gen_maps Fs gs' (Datatypes.S i) f1 in (g1 :: r, f2)
  end.
Fixpoint gen_allow (Fs : list (sst * smodel * tree lin)) (gs : list (lin * Z)) (i : nat) (fresh : positive) : list (lin * Z) * positive :=
  match gs with
  | [] => ([], fresh)
  | g :: gs' => let ok := forallb (fun '(_, MF, σ) => match List.nth_error (sm_allow MF) i with Some g' => lin_eqb (fst g') (lsubst σ (fst g)) | None => false end) Fs in
                let '(g1, f1) := if ok then (g, fresh) else ((lvar fresh, snd g), Pos.succ fresh) in
                let '(r, f2) := gen_allow Fs gs' (Datatypes.S i) f1 in (g1 :: r, f2)
  end.
Definition gen_brk (Fs : list (sst * smodel * tree lin)) (l : lin) (fresh : positive) : lin * positive :=
  if forallb (fun '(_, MF, σ) => lin_eqb (sm_brk MF) (lsubst σ l)) Fs then (l, fresh) else (lvar fresh, Pos.succ fresh).
Definition refineM (T : sst) (MT : smodel) : sst * smodel :=
  let Fs := List.map (fun F => (fst F, snd F, sig F T MT)) FIN6 in
  let '(ms', f1) := gen_maps Fs (sm_maps MT) O (s_next T) in
  let '(al', f2) := gen_allow Fs (sm_allow MT) O f1 in
  let '(brk', f3) := gen_brk Fs (sm_brk MT) f2 in
  (SST (s_pc T) (s_regs T) (s_rgs T) (s_facts T) f3 (s_resv T),
   SM ms' al' (sm_zr MT) (sm_tid MT) brk' (sm_sbrk MT) (sm_sp MT) (sm_frz MT) (sm_own MT)).
Definition TM1 : sst * smodel := refineM T0 MT0.
Definition T1s : sst := sep4 (fst TM1) (snd TM1).
Definition T2 : sst := refine T1s (snd TM1).
Definition T3 : sst := refine T2 (snd TM1).
Definition MT3 : smodel := snd TM1.
(* [comment removed for export] *)
Definition TMAIN : sst := Eval vm_compute in T3.
Definition MMAIN : smodel := Eval vm_compute in MT3.
Definition AMAIN : ast := Eval vm_compute in AT0.
(* [comment removed for export] *)
Definition tm_bridge (F : sst * smodel) : bool :=
  match conv1 F with
  | Some (S', M', a') => let σ := sig (S', M') TMAIN MMAIN in (entails S' TMAIN σ && sm_eqb M' (msubst σ MMAIN) && aeqb a' (asubst σ AMAIN))%bool
  | None => false
  end.
Lemma tm_bridge_all : forallb tm_bridge (FINC ++ FINA ++ FINB) = true.
Proof. vm_compute. reflexivity. Qed.
