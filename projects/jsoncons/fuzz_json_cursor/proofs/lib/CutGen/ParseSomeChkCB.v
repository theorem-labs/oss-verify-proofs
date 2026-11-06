(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA PmLibDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutShA CutShB CutShC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_cboth_T Cut_psome_cboth_D Cut_psome_cboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsoInstCB PsoKnCB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSO.

Module G.
Definition CPS := Cut_psome_cboth_D.CPS. Definition BLS := Cut_psome_cboth_D.BLS. Definition TAGS := Cut_psome_cboth_D.TAGS. Definition RETS := Cut_psome_cboth_D.RETS.
Definition HDECL := Cut_psome_cboth_T.HDECL. Definition cp0 := Cut_psome_cboth_D.cp0.
Definition plans := Cut_psome_cboth.plans. Definition tags_ok := Cut_psome_cboth.tags_ok. Definition NF_le := Cut_psome_cboth.NF_le.
End G.
Module GT.
Definition NF := Cut_psome_cboth_T.NF. Definition HDECL := Cut_psome_cboth_T.HDECL. Definition SCELLS := Cut_psome_cboth_T.SCELLS. Definition GLO := Cut_psome_cboth_T.GLO. Definition GHI := Cut_psome_cboth_T.GHI.
Definition t0 := Cut_psome_cboth_T.t0. Definition t1 := Cut_psome_cboth_T.t1.
End GT.
Import PSOC.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.
Definition NCUT : nat := 275.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition cutn (i : nat) : CC.cutpoint := nth i G.CPS CA.dummy_cp.

Record pv : Type := PV { v_level : expr; v_wend : expr; v_wptr : expr; v_st : expr; v_sst : expr; v_nst : expr; v_more : expr; v_done : expr;
                         v_cap1 : expr; v_size : expr; v_bptr : expr; v_sb : expr; v_send : expr; v_scend : expr; v_ec : option expr }.
Definition cellP (cells : list kentry) (off : Z) (w : nat) : option expr := CAX.cell_at cells PE off w.
Definition pview (cells : list kentry) : option pv :=
  match cellP cells 144 4, cellP cells 192 8, cellP cells 200 8, cellP cells 208 1, cellP cells 209 1, cellP cells 210 1, cellP cells 211 1, cellP cells 212 1 with
  | Some a, Some b, Some c, Some d, Some e, Some f, Some g, Some h =>
      match cellP cells 224 8, cellP cells 232 8, cellP cells 240 8, cellP cells 248 8, cellP cells 256 8, cellP cells 264 8 with
      | Some k, Some l, Some m, Some n, Some o, Some p => Some (PV a b c d e f g h k l m n o p (CAX.cell_at cells EE 0 4))
      | _, _, _, _, _, _ => None
      end
  | _, _, _, _, _, _, _, _ => None
  end.

Definition pin (cells : list kentry) (v : nat) : option Z :=
  match find (fun X => match X with KRange (EVar v') lo hi => (Nat.eqb v' v && Z.eqb lo hi)%bool | _ => false end) cells with Some (KRange _ lo _) => Some lo | _ => None end.

Definition st_lit (cells : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some z
  | EAlu Instr.ALU_ADD (EVar v) (ELit k) => match pin cells v with Some z => Some (z + k) | None => None end
  | EVar v => pin cells v
  | _ => None
  end.
Definition inb (z : Z) (l : list Z) : bool := existsb (Z.eqb z) l.

Inductive kind : Set := KEntry | KSm | KH | KHQ | KL | KLQ | KLZ | KL2 | KL3 | KCsl | KRetx | KSe | KSetsh | KErrh | KSetec | KPop | KParent | KVpush | KPushb | KPt (pc : Z) | KVis | KDead.
Definition kind_eqb (a b : kind) : bool :=
  match a, b with
  | KEntry, KEntry | KSm, KSm | KH, KH | KHQ, KHQ | KL, KL | KLQ, KLQ | KLZ, KLZ | KL2, KL2 | KL3, KL3 | KCsl, KCsl | KRetx, KRetx | KSe, KSe | KSetsh, KSetsh
  | KErrh, KErrh | KSetec, KSetec | KPop, KPop | KParent, KParent | KVpush, KVpush | KPushb, KPushb | KVis, KVis | KDead, KDead => true
  | KPt p, KPt q => Z.eqb p q
  | _, _ => false
  end.
Lemma kind_eqb_eq : forall a b, kind_eqb a b = true -> a = b.
Proof. intros [] [] H; try discriminate H; try reflexivity. cbn in H. apply Z.eqb_eq in H. subst. reflexivity. Qed.
Definition is_loopk (k : kind) : bool := match k with KH | KHQ | KL | KLQ | KLZ | KL2 | KL3 | KCsl => true | _ => false end.
Definition is_ptk (k : kind) : bool := match k with KPt _ => true | _ => false end.
Definition decl_kind (i : nat) : kind := nth i [KEntry; KEntry; KH; KHQ; KL; KLQ; KLZ; KL2; KL3; KRetx; KSe] KCsl.
Definition ret_kind (pc : Z) : kind :=
  if Z.eqb pc SM4 then KSm else if Z.eqb pc SETSH then KSetsh else if Z.eqb pc ERRH then KErrh else if Z.eqb pc SETEC then KSetec
  else if Z.eqb pc POPST then KPop else if Z.eqb pc PARENT then KParent else if Z.eqb pc VPUSH then KVpush else if Z.eqb pc PUSHB then KPushb
  else if Z.eqb pc VNULL then KVis else if Z.eqb pc VBOOL then KVis else KPt pc.

Definition src_of (j : nat) : option (nat * nat * Z) :=
  match find (fun r : nat * nat * nat * Z => let '(j', _, _, _) := r in Nat.eqb j' j) G.RETS with Some (_, i, k, pc) => Some (i, k, pc) | None => None end.
Definition leaf_cells (i k : nat) : list kentry := SR.ps_cells (nth k (CC.cp_PSS (cutn i)) (SR.PS 0 [] [] [])).

Definition hq_dead (cells : list kentry) : bool := match pin cells IDXV with Some z => negb (inb (z + 1) QSTATES) | None => false end.

Definition info_step (acc : list (kind * bool)) (j : nat) : list (kind * bool) :=
  acc ++ [if Nat.ltb j NDECL then (decl_kind j, Nat.ltb j 2) else
          match src_of j with
          | Some (i, k, pc) =>
              let '(ki, ui) := nth i acc (KDead, false) in
              (if (kind_eqb ki KDead || (kind_eqb ki KHQ && hq_dead (leaf_cells i k)))%bool then KDead else ret_kind pc, ui)
          | None => (KDead, false)
          end].
Definition INFO : list (kind * bool) := Eval vm_compute in fold_left info_step (seq 0 NCUT) [].
Definition kind_of (i : nat) : kind := fst (nth i INFO (KDead, false)).
Definition u0 (i : nat) : bool := snd (nth i INFO (KDead, false)).
Definition isQcut (i : nat) : bool := (kind_eqb (kind_of i) KHQ || kind_eqb (kind_of i) KLQ)%bool.

Definition CSP : Z := -672.
Definition FR : expr * Z * Z := (FE, 4, CSP).
Definition FFS : list (list (expr * Z * Z)) := Eval vm_compute in ([] :: [] :: repeat [FR] (NCUT - 2)).
Definition blk0 (i : nat) : expr * expr := hd (ELit 0, ELit 0) (nth i G.BLS []).
Definition blk1 (i : nat) : expr * expr := hd (ELit 0, ELit 0) (tl (nth i G.BLS [])).

Definition F_STK : SGP.region := (EVar 2, - SCR, ELit SCR).
Definition F0 : list SGP.region := [F_STK; (PE, 208, ELit 1); (PE, 211, ELit 1); (PE, 212, ELit 1)].
Definition FP : list SGP.region := [(PE, 148, ELit 44); (PE, 200, ELit 16); (PE, 220, ELit 4); (PE, 232, ELit 8)].
Definition F_NB : list SGP.region := [F_STK; (FE, 0, ELit 24); (FE, 32, ELit 984); (CHA.SRL3 FE, SBz, ELit 128)] ++ FP.
Definition MORE : SGP.region := (PE, 211, ELit 1).
Definition region_eqb (x y : SGP.region) : bool := (expr_eqb (fst (fst x)) (fst (fst y)) && Z.eqb (snd (fst x)) (snd (fst y)) && expr_eqb (snd x) (snd y))%bool.

Definition UEXTRA : list SGP.region := [MORE; (FLE, 0, ELit 1); (PE, 208, ELit 1); (PE, 212, ELit 1); (FE, 0, ELit 8)].
Definition cpf_ok (i : nat) (F : list SGP.region) : bool :=
  forallb (fun r => (existsb (region_eqb r) (F_NB ++ UEXTRA) || region_eqb r (fst (blk0 i), 0, ELit 1))%bool) F.

Definition SID : CC.subst := map (fun k => (k, EVar k)) (seq 40 60).
Definition CURH : expr := EAlu Instr.ALU_ADD WLEN (EAlu Instr.ALU_ADD WP0 (EMd Instr.M_MUL (ELit (-1)) (EVar JV))).
Definition CURR : expr := EAlu Instr.ALU_ADD CURH (ELit 1).

Definition ROWTAB : list (nat * Z * nat * nat * nat * Z * Z * Z) := [(2%nat, 753476, 11%nat, 10%nat, 10%nat, 60, 36, 1); (3%nat, 753476, 11%nat, 10%nat, 10%nat, 38, 36, 1); (2%nat, 753624, 12%nat, 10%nat, 10%nat, 60, 36, 27); (2%nat, 754112, 13%nat, 10%nat, 10%nat, 60, 36, 24); (2%nat, 754240, 14%nat, 10%nat, 10%nat, 60, 36, 11); (3%nat, 754240, 14%nat, 10%nat, 10%nat, 38, 36, 11); (2%nat, 754456, 15%nat, 10%nat, 10%nat, 60, 36, 23); (2%nat, 755020, 16%nat, 10%nat, 10%nat, 60, 36, 10); (3%nat, 755020, 16%nat, 10%nat, 10%nat, 38, 36, 10); (2%nat, 755312, 17%nat, 10%nat, 10%nat, 60, 36, 21); (2%nat, 755440, 18%nat, 10%nat, 10%nat, 60, 36, 25); (2%nat, 755556, 19%nat, 10%nat, 10%nat, 60, 36, 18); (2%nat, 755716, 20%nat, 10%nat, 10%nat, 60, 36, 20); (2%nat, 753896, 21%nat, 10%nat, 10%nat, 60, 36, 13); (3%nat, 753896, 21%nat, 10%nat, 10%nat, 38, 36, 13); (2%nat, 755920, 22%nat, 10%nat, 10%nat, 60, 36, 5); (3%nat, 755920, 22%nat, 10%nat, 10%nat, 38, 36, 5); (2%nat, 756104, 23%nat, 10%nat, 10%nat, 60, 36, 19); (2%nat, 756220, 24%nat, 10%nat, 10%nat, 60, 36, 6); (2%nat, 756280, 25%nat, 10%nat, 10%nat, 60, 36, 3); (2%nat, 756460, 26%nat, 10%nat, 10%nat, 60, 36, 9); (3%nat, 756460, 26%nat, 10%nat, 10%nat, 38, 36, 9); (2%nat, 756668, 27%nat, 10%nat, 10%nat, 60, 58, 4); (2%nat, 756896, 28%nat, 10%nat, 10%nat, 60, 36, 7); (3%nat, 756896, 28%nat, 10%nat, 10%nat, 38, 36, 7); (2%nat, 757108, 29%nat, 10%nat, 10%nat, 60, 36, 22); (2%nat, 757260, 30%nat, 10%nat, 10%nat, 60, 58, 28); (2%nat, 754808, 31%nat, 10%nat, 10%nat, 60, 36, 12); (3%nat, 754808, 31%nat, 10%nat, 10%nat, 38, 36, 12); (2%nat, 757448, 32%nat, 10%nat, 10%nat, 60, 36, 26); (11%nat, 758972, 33%nat, 11%nat, 11%nat, 36, 34, 1); (21%nat, 759364, 34%nat, 11%nat, 11%nat, 36, 34, 13); (31%nat, 759764, 35%nat, 11%nat, 11%nat, 36, 34, 12); (11%nat, 768068, 36%nat, 11%nat, 11%nat, 36, 34, 1); (21%nat, 768656, 37%nat, 11%nat, 11%nat, 36, 34, 13); (31%nat, 769044, 38%nat, 11%nat, 11%nat, 36, 34, 12)].

Definition mkrow (r : nat * Z * nat * nat * nat * Z * Z * Z) : CSLR.row :=
  let '(i, pc, j, rd, rs, a, b, _) := r in CSLR.ROW i pc j SID rd rs CURH a b false.
Definition ROWS : list CSLR.row := map mkrow ROWTAB.
Definition KZB : kentry := CSLR.KZB SBz CH CHG.
Definition KZT : kentry := KZero (SA (ELit 0) 0) (ELit 0).

Inductive fd : Set := Same | Lit (z : Z) | Var (v : nat) | Other.
Definition fdelta (a b : expr) : fd := if expr_eqb a b then Same else match b with ELit z => Lit z | EVar v => Var v | _ => Other end.
Definition fdelta_o (a b : option expr) : fd := match a, b with Some x, Some y => fdelta x y | _, None => Same | None, Some _ => Other end.
Record delta : Set := DL { d_level : fd; d_wend : fd; d_wptr : fd; d_st : fd; d_sst : fd; d_nst : fd; d_more : fd; d_done : fd;
                           d_cap1 : fd; d_size : fd; d_bptr : fd; d_sb : fd; d_send : fd; d_scend : fd; d_ec : fd; d_adv : Z }.
Definition rng_is (cells : list kentry) (e : expr) (v : Z) : bool := match CX.range3 cells e with Some (lo, hi) => (Z.eqb lo v && Z.eqb hi v)%bool | None => false end.

Definition fnorm (cells : list kentry) (f : fd) : fd :=
  match f with Var v => match CX.range3 cells (EVar v) with Some (lo, hi) => if Z.eqb lo hi then Lit lo else f | None => f end | _ => f end.
Definition mkdelta (cells : list kentry) (t l : pv) : delta :=
  DL (fdelta (v_level t) (v_level l)) (fdelta (v_wend t) (v_wend l)) (fdelta (v_wptr t) (v_wptr l)) (fdelta (v_st t) (v_st l)) (fnorm cells (fdelta (v_sst t) (v_sst l)))
     (fnorm cells (fdelta (v_nst t) (v_nst l))) (fnorm cells (fdelta (v_more t) (v_more l))) (fnorm cells (fdelta (v_done t) (v_done l))) (fdelta (v_cap1 t) (v_cap1 l)) (fdelta (v_size t) (v_size l))
     (fdelta (v_bptr t) (v_bptr l)) (fdelta (v_sb t) (v_sb l)) (fdelta (v_send t) (v_send l)) (fdelta (v_scend t) (v_scend l)) (fdelta_o (v_ec t) (v_ec l))
     (if expr_eqb (v_wptr t) (v_wptr l) then 0 else if rng_is cells (APC.esub (v_wptr l) (v_wptr t)) 1 then 1 else -1).
Definition is_same (f : fd) : bool := match f with Same => true | _ => false end.

Definition frame_same (d : delta) : bool :=
  (is_same (d_level d) && is_same (d_wend d) && is_same (d_cap1 d) && is_same (d_bptr d) && is_same (d_sb d) && is_same (d_send d) && is_same (d_scend d) && is_same (d_ec d))%bool.

Definition lo_ge (cells : list kentry) (e : expr) (v : Z) : bool := match CX.range3 cells e with Some (lo, _) => Z.leb v lo | None => false end.
Definition is_curpc (pc : Z) : bool := inb pc [PSTRING; PTRUE; PFALSE; PNUMBER].
Definition curk (k : kind) : bool := match k with KPt pc => is_curpc pc | _ => false end.
Definition wptr_ok (i : nat) (c : CC.cutpoint) (cells : list kentry) (t l : pv) (d : delta) : bool :=
  (is_same (d_wptr d) || (Z.eqb (d_adv d) 1 && lo_ge (CC.cp_know c) (EVar JV) 1) || (curk (kind_of i) && expr_eqb (v_wptr l) (nth 10 (CC.cp_regs c) (ELit 0))))%bool.

Definition has_bufbyte (F : list SGP.region) : bool := existsb (fun r : SGP.region => match r with (EVar v, 0, ELit 1) => negb (Nat.eqb v 2) | _ => false end) F.
Definition size_ok (c : CC.cutpoint) (cells : list kentry) (l : pv) (d : delta) : bool :=
  match d_size d with
  | Same => true
  | Lit 0 => has cells (KWord (SA (v_bptr l) 0) 1 (ELit 0))
  | _ => false
  end.

Definition reg_of (ps : SR.post_spec) (r : nat) : expr := match find (fun ie : nat * expr => Nat.eqb (fst ie) r) (SR.ps_regs ps) with Some (_, e) => e | None => ELit (-1) end.
Definition ret_of (i k : nat) : option (nat * CC.cutpoint) :=
  match CH2.ret_of G.RETS i k with Some j => match nth_error G.CPS j with Some cj => Some (j, cj) | None => None end | None => None end.

Definition gof (ps : SR.post_spec) (i : nat) (c cj : CC.cutpoint) (scr : Z) (ng : nat) : nat :=
  match CHA.common_chk GT.NF G.HDECL scr ng c ps cj (nth i G.BLS []) (nth i FFS []) with Some ci => CH2.ci_nx ci | None => 0%nat end.

Definition callee_x (xa : CAXA.xsumA) (ps : SR.post_spec) (i j : nat) (c cj : CC.cutpoint) : bool :=
  let x := PSOK.x_of xa in let regs := CA.ps_reglist ps in let cells := SR.ps_cells ps in
  let scr := CAX.xs_scr x in let ng := CAX.xs_ng x in let g := gof ps i c cj scr ng in
  let BLk := CAX.xs_keep x regs (nth i G.BLS []) in
  match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr ng BLk (nth i FFS []) (CAX.xs_wregs x regs) (PSOK.news_of xa regs cells g BLk) (CAX.xs_a0 x regs g)
          c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
  | Some ci => (Z.eqb (CH2.ci_csp ci) CSP && CH2.blocks_eqb (nth j G.BLS []) (PSOK.blk_of xa regs cells g BLk)
                && CBA.regions_eqb (CC.cp_F cj) (CAX.xs_F x (CC.cp_F c)))%bool
  | None => false
  end.

Definition handledb (x : Z) : bool := (((1 <=? x) && (x <=? 7)) || ((9 <=? x) && (x <=? 13)) || (x =? 15) || ((17 <=? x) && (x <=? 28)))%bool.
Definition commentb (x : Z) : bool := ((3 <=? x) && (x <=? 6))%bool.
Definition ccrb (x : Z) : bool := (commentb x || (x =? 28))%bool.
Definition expectb (x : Z) : bool := inb x [1; 7; 9; 10; 11; 12; 13].

Definition step_ok (lvl1 : bool) (st1 st2 : Z) : bool :=
  ((commentb st1 && commentb st2)
   || (negb (ccrb st1) && negb (st1 =? 15) && handledb st2 && negb (ccrb st2) && negb (st2 =? 15) && negb (st2 =? 17) && (negb (st2 =? 7) || lvl1)))%bool.

Definition tst (c : CC.cutpoint) (cells : list kentry) (t : pv) : option Z := st_lit (cells ++ CC.cp_know c) (v_st t).
Definition lst (cells : list kentry) (l : pv) : option Z := st_lit cells (v_st l).

Definition lit_in (f : fd) (lo hi : Z) : bool := match f with Same => true | Lit z => (Z.leb lo z && Z.leb z hi)%bool | _ => false end.

Inductive gcase : Set :=
  | GSame
  | GStop
  | GAccept
  | GStep (st1 st2 : Z)
  | GPop (v : nat)
  | GPush (st1 st2 : Z).
Definition more1 (c : CC.cutpoint) (cells : list kentry) (t l : pv) : bool :=
  match v_more l with ELit 1 => true | EVar v => (lo_ge cells (EVar v) 1 || lo_ge (CC.cp_know c) (EVar v) 1)%bool | _ => false end.
Definition morek (f : fd) : option bool := match f with Same | Lit 1 => Some true | Lit 0 => Some false | _ => None end.
Definition gclass (i : nat) (c : CC.cutpoint) (cells : list kentry) (t l : pv) (d : delta) : option gcase :=
  if negb (lit_in (d_sst d) 0 11 && lit_in (d_nst d) 0 7 && lit_in (d_done d) 0 1)%bool then None else
  let lvl1 := lo_ge cells (EVar LEVELV) 1 in
  match morek (d_more d), d_st d with
  | Some true, Same => if (is_same (d_more d) && is_same (d_sst d) && is_same (d_nst d) && is_same (d_done d))%bool then Some GSame
                  else if more1 c cells t l then match tst c cells t with Some s1 => if step_ok lvl1 s1 s1 then Some (GStep s1 s1) else None | None => None end else None
  | Some false, Same => Some GStop
  | Some false, Lit 29 => match tst c cells t, d_done d with Some 2, Lit 1 => Some GAccept | _, _ => Some GStop end
  | Some false, Lit _ => Some GStop
  | Some true, Lit s2 => if negb (more1 c cells t l) then None else
                    match kind_of i, tst c cells t with
                    | KVpush, Some s1 => Some (GPush s1 s2)
                    | _, Some s1 => if step_ok lvl1 s1 s2 then Some (GStep s1 s2) else None
                    | _, None => None
                    end
  | Some true, Var v => if (kind_eqb (kind_of i) KPop && Nat.eqb v (CC.cp_nx c - APC.NCS - 2) && more1 c cells t l && is_same (d_sst d) && is_same (d_nst d))%bool then Some (GPop v) else None
  | _, _ => None
  end.

Definition ecvar (t : pv) : option nat := match v_ec t with Some (EVar v) => Some v | _ => None end.
Definition rx_ok (i : nat) (cells : list kentry) (t l : pv) : bool :=
  (match v_more l with ELit 0 => true | e => rng_is cells e 0 end
   || rng_is cells (APC.esub WE (v_wptr l)) 0 || has cells (KRange (EAlu Instr.ALU_SLTU (v_wptr l) (v_wend l)) 0 0)
   || match ecvar t with Some v => lo_ge cells (EVar v) 1 | None => false end
   || kind_eqb (kind_of i) KSetec)%bool.

Definition st0pin (cells : list kentry) : option Z := pin cells STV.
Definition ne_acc (cells : list kentry) : bool :=
  (has cells (KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EVar STV) (ELit 2)) (ELit 1)) 0 0) || match st0pin cells with Some z => negb (Z.eqb z 2) | None => false end)%bool.
Definition goto_pair_ok (ki kj : kind) : bool :=
  match kj with
  | KH => match ki with KL | KSm => true | _ => false end
  | KHQ => kind_eqb ki KLQ
  | KL | KL2 | KL3 => match ki with KL3 | KL2 | KCsl | KErrh | KPop | KParent | KVpush | KPt _ | KVis => true | _ => false end
  | KLQ | KLZ => match ki with KH | KHQ | KPop | KPt _ => true | _ => false end
  | KRetx => negb (kind_eqb ki KEntry || kind_eqb ki KRetx || kind_eqb ki KSetsh || kind_eqb ki KDead || kind_eqb ki KSe)%bool
  | KSe => match ki with KErrh | KCsl | KSm => true | _ => false end
  | _ => false
  end.

Definition vis_stop_ok (c : CC.cutpoint) (cells : list kentry) (t : pv) (d : delta) : bool :=
  match tst c cells t, d_st d with Some s1, Lit s2 => (step_ok (lo_ge cells (EVar LEVELV) 1) s1 s2 && inb s2 [2; 7])%bool | _, _ => false end.
Definition tgt_ok (i j : nat) (c : CC.cutpoint) (cells : list kentry) (t l : pv) (d : delta) (g : gcase) : bool :=
  match kind_of j with
  | KH => match kind_of i with
          | KSm => (match g with GSame => true | _ => false end && ne_acc cells && lo_ge cells (EVar JV) 1)%bool
          | _ => match g with GSame => true | _ => false end
          end
  | KHQ => match g with GSame => true | _ => false end
  | KL | KL2 | KL3 => match g with GSame | GStep _ _ | GPop _ | GPush _ _ => true | GStop => (kind_eqb (kind_of i) KVis && vis_stop_ok c cells t d)%bool | _ => false end
  | KLQ | KLZ => match g with GAccept | GPop _ => true | GSame => is_ptk (kind_of i) | _ => false end
  | KSe => match g with GStop => true | _ => false end
  | KRetx => (rx_ok i cells t l && match g with GSame | GStop | GAccept | GPop _ => true | _ => false end
             && implb (u0 i) (ne_acc cells || match g with GAccept => true | _ => false end))%bool
  | _ => false
  end.

Definition rng_in (cells : list kentry) (e : expr) (lo hi : Z) : bool := match CX.range3 cells e with Some (a, b) => (Z.leb lo a && Z.leb b hi)%bool | None => false end.
Definition view_ok (nx : nat) (cells : list kentry) (v : pv) : bool :=
  forallb (APC.expr_vars_lt nx) [v_level v; v_wend v; v_wptr v; v_st v; v_sst v; v_nst v; v_more v; v_done v; v_cap1 v; v_size v; v_bptr v; v_sb v; v_send v; v_scend v].
Definition goto_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (s : CC.subst) : bool :=
  match nth_error G.CPS j with
  | Some cj =>
      let cells := SR.ps_cells ps in
      (CC.goto_chk GT.NF c ps cj s && goto_pair_ok (kind_of i) (kind_of j)
       && match pview (CC.cp_know c), pview cells with
          | Some t, Some l => let d := mkdelta cells t l in
              (frame_same d && wptr_ok i c cells t l d && is_same (d_size d) && view_ok (CC.cp_nx c) (CC.cp_know c) t && view_ok (CC.cp_nx c) cells l
               && (negb (has_bufbyte (CC.cp_F c)) || has cells (KWord (SA (APC.eadd (v_size l) (v_bptr l)) 0) 1 (ELit 0)))
               && match gclass i c cells t l d with Some g => tgt_ok i j c cells t l d g | None => false end)
          | _, _ => false end)%bool
  | None => false
  end.

Inductive pcase : Set := PSame | PString (s1 : option Z) | PNumber (s1 : option Z) (n : Z).
Definition pclass (i : nat) (c : CC.cutpoint) (cells : list kentry) (t l : pv) (d : delta) : option pcase :=
  if negb (is_same (d_done d) && lit_in (d_sst d) 0 11 && lit_in (d_nst d) 0 7)%bool then None else
  match morek (d_more d), d_st d, d_sst d, d_nst d with
  | Some true, Same, Same, Same => if is_same (d_more d) then Some PSame else None
  | Some true, Lit 15, Lit 0, Same => Some (PString (tst c cells t))
  | Some true, Lit 17, Same, Lit n => Some (PNumber (tst c cells t) n)
  | _, _, _, _ => None
  end.

Definition byte_rng (cells : list kentry) (l : pv) : option (Z * Z) :=
  match CAX.cell_at cells (v_bptr l) 0 1 with Some e => CX.range3 cells e | None => None end.
Definition zseq (lo hi : Z) : list Z := map (fun n => lo + Z.of_nat n) (seq 0 (Z.to_nat (hi - lo + 1))).
Definition numpre_ok (n : Z) (lo hi : Z) : bool :=
  (Z.leb 0 lo && Z.leb hi 255 && forallb (fun b => match PML.nl_step (-1) b with Some k' => (Z.eqb n k' || (Z.eqb n 2 && Z.eqb k' 1))%bool | None => false end) (zseq lo hi))%bool.
Definition pre_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (pc : Z) : bool :=
  let cells := SR.ps_cells ps in
  match pview (CC.cp_know c), pview cells with
  | Some t, Some l =>
      let d := mkdelta cells t l in
      (frame_same d && (is_same (d_wptr d) || (Z.eqb (d_adv d) 1 && lo_ge (CC.cp_know c) (EVar JV) 1)) && size_ok c cells l d
       && view_ok (CC.cp_nx c) (CC.cp_know c) t && view_ok (CC.cp_nx c) cells l
       && match pclass i c cells t l d with
          | Some PSame => negb (Z.eqb pc PNUMBER) || match tst c cells t with Some 17 => true | _ => false end
          | Some (PString _) => Z.eqb pc PSTRING && match d_size d with Lit 0 => true | _ => false end
          | Some (PNumber _ n) => Z.eqb pc PNUMBER && kind_eqb (kind_of i) KPushb && match byte_rng cells l with Some (lo, hi) => numpre_ok n lo hi | None => false end
          | None => false
          end)%bool
  | _, _ => false
  end.
Definition call_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (pc : Z) : bool :=
  match ret_of i k, PSOK.xs_at pc with
  | Some (j, cj), Some xa =>
      (Z.eqb (SR.ps_pc ps) pc && kind_eqb (kind_of j) (if kind_eqb (kind_of i) KDead then KDead else ret_kind pc)
       && callee_x xa ps i j c cj && pre_chk i c ps pc)%bool
  | _, _ => false
  end.

Definition ISHL : list kentry := PSOK.ISH ++ PSOK.BSHZ.
Definition SMUSER : list kentry :=
  [KDisj (SA FE 0) (ELit 1024) (SA WP0 0) WLEN; KDisj (SA FLE 0) (ELit 1) (SA WP0 0) WLEN;
   KDisj (SA (CHA.SRL3 FE) SBz) (ELit 128) (SA (CHA.SRL3 CH) SBz) CHG;
   KDisj (SA (CHA.SRL3 FE) SBz) (ELit 128) (SA (CHA.SRL3 (EVar PPV)) SBz) (ELit 33);
   KDisj (SA (CHA.SRL3 FE) SBz) (ELit 128) (SA (CHA.SRL3 (EVar SBV)) SBz) (CHA.SRL3 (EAlu Instr.ALU_ADD (EVar SCAPV) (ELit 7)));
   KDisj (SA FE 0) (ELit 1024) (SA VE 8) (ELit 40); KDisj (SA FLE 0) (ELit 1) (SA VE 8) (ELit 40)].
Definition sm_ok (ps : SR.post_spec) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok FS_LO G.HDECL (SR.ps_cells ps) 60 (nth 0 G.BLS []) [] 4 65 60 X || has (ISHL ++ SMUSER) X)%bool.
Definition sm_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  match ret_of i k with
  | Some (j, cj) =>
      (Z.eqb (SR.ps_pc ps) SM4 && kind_eqb (kind_of i) KEntry && kind_eqb (kind_of j) KSm
       && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 (nth i G.BLS []) (nth i FFS []) [] (List.filter (sm_ok ps) (CC.cp_know cj)) None
                c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
          | Some ci => (Nat.eqb (CH2.ci_nx ci) 60 && Z.eqb (CH2.ci_csp ci) CSP)%bool
          | None => false end
       && CH2.blocks_eqb (nth j G.BLS []) (nth i G.BLS []) && CBA.regions_eqb (CC.cp_F c) F0
       && has (SR.ps_cells ps) (KWord (SA PE 208) 1 (EVar STV)) && has (SR.ps_cells ps) (KWord (SA PE 211) 1 (ELit 1)) && has (SR.ps_cells ps) (KWord (SA PE 212) 1 (EVar DONEV)))%bool
  | None => false
  end.
Definition CALLEES : list Z := [SM4; SETSH; ERRH; SETEC; POPST; PARENT; VPUSH; PUSHB; SKIPSP; PNULL; BOBJ; BARR; EOBJ; EARR; BMEMBER; PTRUE; PFALSE; PSTRING; PNUMBER; ENDINT; ENDFRAC; VNULL; VBOOL].

Definition dead_chk (i : nat) (ps : SR.post_spec) (pc : Z) : bool :=
  (kind_eqb (kind_of i) KDead || Z.eqb pc DEAD || (kind_eqb (kind_of i) KHQ && hq_dead (SR.ps_cells ps)) || Z.eqb pc LATCH)%bool.

Definition SETSH_NEWS : list kentry := PSOK.STATICS_UAR ++ [KWord (SA FE 1016) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition F_RETX : list SGP.region := [F_STK; (FE, 0, ELit 8)].
Definition setsh_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  match ret_of i k with
  | Some (j, cj) =>
      (Z.eqb (SR.ps_pc ps) SETSH && kind_eqb (kind_of i) KRetx && kind_eqb (kind_of j) KSetsh && CBA.regions_eqb (CC.cp_F c) F_RETX
       && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
       && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 256 0 (nth i G.BLS []) (nth i FFS []) [(CHA.SRL3 FE, SBz, ELit 128)] SETSH_NEWS None
                c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
          | Some ci => (Z.eqb (CH2.ci_csp ci) CSP && Nat.leb (CC.cp_nx c) (CH2.ci_nx ci))%bool
          | None => false end
       && CH2.blocks_eqb (nth j G.BLS []) (nth i G.BLS [])
       && CL.ps_reg_is ps 18 FE && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD (CHA.SRL3 FE) (ELit SBz)) && CL.ps_reg_is ps 11 (ELit 128)
       && has (SR.ps_cells ps) (KWord (SA FE 1016) 8 FLE))%bool
  | None => false
  end.
Definition F_EXIT : list SGP.region := [F_STK; (FE, 0, ELit 8); (FLE, 0, ELit 1)].
Definition exit_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (kind_eqb (kind_of i) KSetsh && CBA.exit_base_chk GT.NF RET c ps && has (SR.ps_cells ps) (KWord (SA FLE 0) 1 (ELit 0)) && CBA.regions_eqb (CC.cp_F c) F_EXIT
   && match CHA.retire_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) with Some fl => expr_eqb fl FLE | None => false end)%bool.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => (Nat.ltb j NCUT && (kind_eqb (kind_of i) KDead || goto_chk i c ps j s))%bool
  | CC.TOther pc =>
      if dead_chk i ps pc then true
      else if Z.eqb pc RET then exit_chk i c ps
      else if Z.eqb pc SETSH then setsh_chk i c k ps
      else if Z.eqb pc SM4 then sm_chk i c k ps
      else if inb pc CALLEES then call_chk i c k ps pc
      else match CSLR.find_row ROWS i (SR.ps_pc ps) with
           | Some r => CSLR.row_chk GT.NF G.HDECL G.CPS G.BLS FFS (CC.cp_F c) SBz JV WP0 WE 32768 KZB 0 0 KZT i c ps r
           | None => false
           end
  end.

Definition tagc (t : CC.tag) : Z := match t with CC.TGoto j _ => 1000 + Z.of_nat j | CC.TOther pc => pc end.

Definition fails (lo n : nat) : list (nat * nat * Z) :=
  flat_map (fun i => let c := cutn i in let tg := nth i G.TAGS [] in
     flat_map (fun k => let ps := nth k (CC.cp_PSS c) (SR.PS 0 [] [] []) in let t := nth k tg (CC.TOther 0) in if leaf_chk i c k ps t then [] else [(i, k, tagc t)]) (seq 0 (length tg))) (seq lo n).

Definition leaves_rng (lo n : nat) : bool :=
  forallb (fun i => match nth_error G.CPS i, nth_error G.TAGS i with
                    | Some c, Some tg => forallb (fun k => match nth_error (CC.cp_PSS c) k, nth_error tg k with Some ps, Some t => leaf_chk i c k ps t | _, _ => true end) (seq 0 (length tg))
                    | _, _ => true end) (seq lo n).
Definition leaf_at (i k : nat) : bool :=
  match nth_error G.CPS i, nth_error G.TAGS i with
  | Some c, Some tg => match nth_error (CC.cp_PSS c) k, nth_error tg k with Some ps, Some t => leaf_chk i c k ps t | _, _ => true end
  | _, _ => true end.
Definition leaves_ks (i : nat) (ks : list nat) : bool := forallb (leaf_at i) ks.
Lemma leaf_at_sound : forall i k c ps t, leaf_at i k = true -> CH2.is_leaf G.CPS G.TAGS i c k ps t -> leaf_chk i c k ps t = true.
Proof. intros i k c ps t H (tags & Hc & Htg & Hps & Ht). unfold leaf_at in H. rewrite Hc, Htg, Hps, Ht in H. exact H. Qed.
Lemma leaves_ks_sound : forall i ks, leaves_ks i ks = true -> forall k c ps t, In k ks -> CH2.is_leaf G.CPS G.TAGS i c k ps t -> leaf_chk i c k ps t = true.
Proof. intros i ks H k c ps t Hk IL. unfold leaves_ks in H. rewrite forallb_forall in H. exact (leaf_at_sound i k c ps t (H k Hk) IL). Qed.
Lemma len_cps : length G.CPS = 275%nat. Proof. vmc_refl. Qed.
Lemma leaves_rng_sound : forall lo n, leaves_rng lo n = true ->
  forall i c k ps t, (lo <= i < lo + n)%nat -> CH2.is_leaf G.CPS G.TAGS i c k ps t -> leaf_chk i c k ps t = true.
Proof.
  intros lo n H i c k ps t Hi (tags & Hc & Htg & Hps & Ht). unfold leaves_rng in H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; exact Hi)). rewrite Hc, Htg in H. rewrite forallb_forall in H.
  assert (Hk : (k < length tags)%nat) by (apply nth_error_Some; rewrite Ht; discriminate).
  specialize (H k ltac:(apply in_seq; split; [apply Nat.le_0_l | exact Hk])). rewrite Hps, Ht in H. exact H.
Qed.
End PSO.
