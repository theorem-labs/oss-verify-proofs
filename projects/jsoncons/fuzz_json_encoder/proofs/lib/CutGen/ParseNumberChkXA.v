(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA PmLibDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutShA CutShB CutShC.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_pn_xasan_T Cut_pn_xasan_D Cut_pn_xasan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsKitA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PNA.
(* [comment removed for export] *)
Module G.
Definition CPS := Cut_pn_xasan_D.CPS. Definition BLS := Cut_pn_xasan_D.BLS. Definition TAGS := Cut_pn_xasan_D.TAGS. Definition RETS := Cut_pn_xasan_D.RETS.
Definition HDECL := Cut_pn_xasan_T.HDECL. Definition cp0 := Cut_pn_xasan_D.cp0.
Definition plans := Cut_pn_xasan.plans. Definition tags_ok := Cut_pn_xasan.tags_ok. Definition NF_le := Cut_pn_xasan.NF_le.
End G.
Module GT.
Definition NF := Cut_pn_xasan_T.NF. Definition HDECL := Cut_pn_xasan_T.HDECL. Definition SCELLS := Cut_pn_xasan_T.SCELLS. Definition GLO := Cut_pn_xasan_T.GLO. Definition GHI := Cut_pn_xasan_T.GHI.
Definition t0 := Cut_pn_xasan_T.t0.
End GT.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.
Definition PC_SM : Z := 417764. Definition PC_APPR : Z := 911564. Definition PC_ENDI : Z := 876732. Definition PC_ENDF : Z := 876908.
Definition PC_SETEC : Z := 827600. Definition PC_ERRH : Z := 836392. Definition RETPC : Z := 891068.
Definition SBz : Z := 2147450880. Definition GD : Z := 6931840. Definition AXT : Z := 7069728. Definition ERRNO : Z := 6938412. Definition ISH2 : Z := 2147628550.
Definition TAB : Z := 165728. Definition TLO : Z := 165728. Definition TG : Z := 32. Definition TSH : Z := 2147471596.   (* [comment removed for export] *)
Definition PE := EVar 10. Definition CUR0 := EVar 11. Definition VE := EVar 12. Definition EE := EVar 13.
Definition WLEN := EVar 32. Definition BX := EVar 33. Definition K0 := EVar 34. Definition SIZE0 := EVar 35. Definition P0 := EVar 36. Definition SBX := EVar 37. Definition SLEN := EVar 38.
Definition SCAP := EVar 39. Definition NST0 := EVar 42. Definition CH := EVar 47. Definition FLE := EVar 50. Definition JV := EVar 51. Definition FE := EVar 55. Definition BYTE := EVar 73.
Definition WEND : expr := EAlu Instr.ALU_ADD CUR0 WLEN.
Definition CUR : expr := EAlu Instr.ALU_ADD CUR0 (EAlu Instr.ALU_ADD WLEN (EMd Instr.M_MUL (ELit (-1)) JV)).     (* [comment removed for export] *)
Definition TADDR : expr := EAlu Instr.ALU_ADD BYTE (ELit TAB).                                                 (* [comment removed for export] *)
Definition NCUT : nat := 74.

(* [comment removed for export] *)
Inductive kind : Set := KEntry | KDecl | KRetx | KSm | KAppr | KErrh | KSetec | KEnd.
Definition kind_eqb (a b : kind) : bool :=
  match a, b with KEntry, KEntry | KDecl, KDecl | KRetx, KRetx | KSm, KSm | KAppr, KAppr | KErrh, KErrh | KSetec, KSetec | KEnd, KEnd => true | _, _ => false end.
Lemma kind_eqb_eq : forall a b, kind_eqb a b = true -> a = b. Proof. intros [] [] H; try discriminate; reflexivity. Qed.
Definition ret_of_kind (pc : Z) : kind :=
  if Z.eqb pc PC_SM then KSm else if Z.eqb pc PC_APPR then KAppr else if Z.eqb pc PC_ERRH then KErrh else if Z.eqb pc PC_SETEC then KSetec else KEnd.
Definition RETXI : nat := 47.      (* [comment removed for export] *)
Definition kind_of (j : nat) : kind :=
  if Nat.eqb j 0 then KEntry else if Nat.eqb j RETXI then KRetx else
  match find (fun r : nat * nat * nat * Z => let '(j', _, _, _) := r in Nat.eqb j j') G.RETS with
  | Some (_, _, _, pc) => ret_of_kind pc
  | None => KDecl
  end.
(* [comment removed for export] *)
Definition minus_fam (i : nat) : bool := existsb (Nat.eqb i) [1; 14; 22; 36; 39; 55; 71]%nat.
Definition curE (i : nat) : expr := if minus_fam i then CUR0 else CUR.          (* [comment removed for export] *)
Definition jrem (i : nat) : expr := if minus_fam i then WLEN else JV.           (* [comment removed for export] *)
Definition mvar (i : nat) : nat := if minus_fam i then 32%nat else 51%nat.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FR : expr * Z * Z := (FE, 1, -160).
Definition FFS : list (list (expr * Z * Z)) := [] :: repeat [FR] 73.
Definition blk0 (i : nat) : expr * expr := hd (ELit 0, ELit 0) (nth i G.BLS []).
Definition blk1 (i : nat) : expr * expr := hd (ELit 0, ELit 0) (tl (nth i G.BLS [])).

(* [comment removed for export] *)
Definition SID : CC.subst := map (fun k => (k, EVar k)) (seq 50 24).
Definition KZB : kentry := CSLR.KZB SBz CH (ELit 2048).
Definition KZT : kentry := CSLR.KZT TG TSH.
Definition ROWS : list CSLR.row :=
  [CSLR.ROW 1 888604 14 SID 10 10 CUR0 40 38 false; CSLR.ROW 2 888680 15 SID 10 10 CUR 40 38 false; CSLR.ROW 9 888716 16 SID 10 10 CUR 36 34 false;
   CSLR.ROW 11 888796 17 SID 10 10 CUR 30 28 false; CSLR.ROW 12 889620 18 SID 10 10 CUR 30 28 false; CSLR.ROW 6 890192 19 SID 10 10 CUR 40 38 false;
   CSLR.ROW 7 890228 20 SID 10 10 CUR 40 38 false; CSLR.ROW 13 890308 21 SID 10 10 CUR 30 28 false;
   CSLR.ROW 14 888636 22 SID 13 13 TADDR 38 36 true; CSLR.ROW 15 889324 23 SID 12 12 TADDR 38 36 true; CSLR.ROW 16 888748 24 SID 12 12 TADDR 34 32 true;
   CSLR.ROW 17 888820 25 SID 13 13 TADDR 28 26 true; CSLR.ROW 18 889644 26 SID 14 14 TADDR 28 26 true; CSLR.ROW 19 890608 27 SID 13 13 TADDR 38 36 true;
   CSLR.ROW 20 890260 28 SID 12 12 TADDR 38 36 true; CSLR.ROW 21 890332 29 SID 13 13 TADDR 28 26 true].
(* [comment removed for export] *)
Definition F0 : list SGP.region := [(EVar 2, -16896, ELit 16896); (PE, 168, ELit 8); (PE, 210, ELit 1)].
Definition FRM3 : list SGP.region := [(FE, 0, ELit 24); (FE, 32, ELit 88); (CHA.SRL3 FE, SBz, ELit 16)].
Definition FLR : SGP.region := (FLE, 0, ELit 1).
Definition MORE : SGP.region := (PE, 211, ELit 1).
Definition CPF_N : list SGP.region := F0 ++ FRM3.                   (* [comment removed for export] *)
Definition CPF_NM : list SGP.region := F0 ++ FRM3 ++ [MORE].        (* [comment removed for export] *)
Definition CPF_MM : list SGP.region := F0 ++ FRM3 ++ [MORE; MORE].  (* [comment removed for export] *)
Definition CPF_E : list SGP.region := [(EVar 2, -16896, ELit 16896); (FE, 0, ELit 24); (FE, 32, ELit 88); (CHA.SRL3 FE, SBz, ELit 16)].   (* [comment removed for export] *)
Definition CPF_X : list SGP.region := [(EVar 2, -16896, ELit 16896); (FE, 0, ELit 24); (CHA.SRL3 FE, SBz, ELit 16); FLR].              (* [comment removed for export] *)
Definition cpf_of_kind (k : kind) : list SGP.region :=
  match k with KEntry => F0 | KRetx => CPF_X | KErrh => CPF_NM | KSetec => CPF_MM | KEnd => CPF_E | _ => CPF_N end.
(* [comment removed for export] *)
Definition UREGS : list SGP.region := [(EVar 2, -16896, ELit 16896); (PE, 168, ELit 8); (PE, 210, ELit 1); (PE, 211, ELit 1);
                                       (FE, 0, ELit 24); (FE, 32, ELit 88); (CHA.SRL3 FE, SBz, ELit 16); FLR].
Definition region_eqb (x y : SGP.region) : bool := (expr_eqb (fst (fst x)) (fst (fst y)) && Z.eqb (snd (fst x)) (snd (fst y)) && expr_eqb (snd x) (snd y))%bool.
Definition cpf_ok (F : list SGP.region) : bool := forallb (fun r => existsb (region_eqb r) UREGS) F.

Definition has := CC.has_cell.
Definition STAT : list kentry := [KImg 1444792 1448528; KWord (SA (ELit 0) 1482488) 8 (ELit SBz); KWord (SA (ELit 0) 1482496) 4 (ELit 1)].
Definition ISHL : list kentry := [KZero (SA (ELit 0) ISH2) (ELit 1); KZero (SA (ELit 0) TSH) (ELit TG)].
Definition FLAG : list kentry := [KWord (SA FE 120) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition NEWS_F : list kentry := STAT ++ ISHL ++ FLAG.
Definition SETEC_W : list SGP.region := [(EE, 0, ELit 16); (ELit 0, GD, ELit 2); (ELit 0, AXT, ELit 544)].
Definition STR_W : list SGP.region := [(PE, 224, ELit 24)].
Definition END_W : list SGP.region := [(PE, 0, ELit 272); (EE, 0, ELit 16); (ELit 0, GD, ELit 2); (ELit 0, AXT, ELit 544)].
Definition ENDE_W : list SGP.region := END_W ++ [(ELit 0, ERRNO, ELit 4)].
Definition S2E := EVar 49.          (* [comment removed for export] *)
Definition LITLO : Z := 6931848.    (* [comment removed for export] *)
Definition WENC : list SGP.region := [(VE, 264, ELit 40); (VE, 400, ELit 4); (S2E, 0, ELit 24); (ELit 0, LITLO, ELit 72)].   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition size_of (cells : list kentry) : expr := match CAX.cell_at cells PE 232 8 with Some e => e | None => ELit 0 end.
Definition STR_NEWS (g : nat) (sz : expr) : list kentry :=
  let cap := APC.escale 2 (EVar (g + 1)%nat) in
  [KWord (SA PE 224) 8 (APC.eaddz cap 1); KWord (SA PE 232) 8 sz; KWord (SA PE 240) 8 (EVar g);
   KRange (EVar (g + 1)%nat) 132 67108864; KRange (APC.esub (APC.eaddz cap (-1)) sz) 0 140737488355328; KAlign cap 8].
(* [comment removed for export] *)
Definition END_NEWS (g : nat) : list kentry :=
  [KWord (SA EE 0) 4 (EVar g); KRange (EVar g) 0 31; KWord (SA PE 240) 8 (EVar (g + 1)%nat); KWord (SA PE 224) 8 (APC.eaddz (APC.escale 2 (EVar (g + 2)%nat)) 1);
   KWord (SA PE 248) 8 (EVar (g + 3)%nat); KWord (SA PE 264) 8 (APC.eadd (EVar (g + 3)%nat) (EVar (g + 4)%nat))].
(* [comment removed for export] *)
Definition SMUSER : list kentry := [KDisj (SA FE 0) (ELit 128) (SA CUR0 0) WLEN; KDisj (SA FLE 0) (ELit 1) (SA CUR0 0) WLEN].
Definition sm_ok (ps : SR.post_spec) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok 7077888 G.HDECL (SR.ps_cells ps) 50 (nth 0 G.BLS []) [] 1 55 50 X || CC.has_cell (ISHL ++ SMUSER) X)%bool.
(* [comment removed for export] *)
Definition callee (ps : SR.post_spec) (i j : nat) (c cj : CC.cutpoint) (scr : Z) (ng : nat) (BLk : CA.blocks) (wregs : list SGP.region) (news : list kentry) (a0x : option expr) : bool :=
  match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr ng BLk (nth i FFS []) wregs news a0x c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
  | Some ci => Z.eqb (CH2.ci_csp ci) (-160)
  | None => false
  end.
(* [comment removed for export] *)
Definition gof (ps : SR.post_spec) (i : nat) (c cj : CC.cutpoint) (scr : Z) (ng : nat) : nat :=
  match CHA.common_chk GT.NF G.HDECL scr ng c ps cj (nth i G.BLS []) (nth i FFS []) with Some ci => CH2.ci_nx ci | None => 0%nat end.
Definition ret_of (i k : nat) : option (nat * CC.cutpoint) :=
  match CH2.ret_of G.RETS i k with Some j => match nth_error G.CPS j with Some cj => Some (j, cj) | None => None end | None => None end.
Definition reg_of (ps : SR.post_spec) (r : nat) : expr := match find (fun ie : nat * expr => Nat.eqb (fst ie) r) (SR.ps_regs ps) with Some (_, e) => e | None => ELit (-1) end.   (* [comment removed for export] *)
Lemma reg_of_is : forall ps r e, reg_of ps r = e -> e <> ELit (-1) -> CL.ps_reg_is ps r e = true.
Proof.
  intros ps r e H Hne. unfold reg_of in H. destruct (find _ (SR.ps_regs ps)) as [[n e']|] eqn:Hf; [|exfalso; exact (Hne (eq_sym H))].
  apply find_some in Hf as [Hin Hn]. cbn [fst] in Hn. subst e'. unfold CL.ps_reg_is. apply existsb_exists. exists (n, e). split; [exact Hin|]. cbn [fst snd]. rewrite Hn, APS.expr_eqb_refl'. reflexivity.
Qed.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition prove (cells : list kentry) (X : kentry) : bool := if APC.fact_ok cells X then true else PPVA.prove3 cells X.

(* [comment removed for export] *)
Definition cut_states (i : nat) : option (list Z) :=
  nth i [None; Some [0]; Some [1]; Some [1; 2]; Some [3]; Some [4]; Some [5]; Some [6]; Some [7];        (* [comment removed for export] *)
         Some [3]; Some [7]; Some [4]; Some [1; 2]; Some [7];                                            (* [comment removed for export] *)
         Some [0]; Some [1]; Some [3]; Some [4]; Some [1; 2]; Some [5]; Some [6]; Some [7];               (* [comment removed for export] *)
         Some [0]; Some [1]; Some [3]; Some [4]; Some [1; 2]; Some [5]; Some [6]; Some [7];               (* [comment removed for export] *)
         Some [4]; Some [1; 2]; Some [7]; Some [1];                                                       (* [comment removed for export] *)
         None; None; None; None; None;                                                                    (* [comment removed for export] *)
         Some [0]; Some [1]; Some [1; 2]; Some [3]; Some [4]; Some [5]; Some [6]; Some [7];               (* [comment removed for export] *)
         None] None.                                                                                      (* [comment removed for export] *)
Definition entry_states (c : Z) : list Z := if Z.eqb c 2 then [1; 2] else [c].       (* [comment removed for export] *)
Definition nst_ok (c k : Z) : bool := (Z.eqb k c || (Z.eqb c 2 && Z.eqb k 1))%bool.   (* [comment removed for export] *)
Definition final_ok (k : Z) : bool := existsb (Z.eqb k) [1; 2; 4; 7].
Definition zseq (lo hi : Z) : list Z := map (fun n => lo + Z.of_nat n) (seq 0 (Z.to_nat (hi - lo + 1))).
Definition step_chk (Si : list Z) (lo hi : Z) (okf : Z -> bool) : bool :=
  forallb (fun v => forallb (fun k => match PML.nl_step k v with Some k' => okf k' | None => false end) Si) (zseq lo hi).
(* [comment removed for export] *)
Definition rng_is (cells : list kentry) (e : expr) (v : Z) : bool := match CX.range3 cells e with Some (lo, hi) => (Z.eqb lo v && Z.eqb hi v)%bool | None => false end.
Definition lo_ge (cells : list kentry) (e : expr) (v : Z) : bool := match CX.range3 cells e with Some (lo, _) => Z.leb v lo | None => false end.
(* [comment removed for export] *)
Definition named_at (cells : list kentry) (cur : expr) : option (saddr * expr * Z * Z) :=
  match find (fun X => match X with KWord a 1 _ => rng_is cells (APC.esub (APC.eaddz (a_base a) (a_off a)) cur) 0 | _ => false end) cells with
  | Some (KWord a 1 v) => match CX.range3 cells v with
                          | Some (lo, hi) => if (Z.leb 0 lo && Z.leb hi 255)%bool then Some (a, v, lo, hi) else None
                          | None => None end
  | _ => None
  end.
(* [comment removed for export] *)
Definition content_chk (i : nat) (cells : list kentry) (dist : expr) (okf : Z -> bool) : bool :=
  match cut_states i with
  | None => false
  | Some Si =>
      if rng_is cells dist 0 then forallb okf Si
      else if (rng_is cells dist 1 && lo_ge cells (jrem i) 1 && CC.has_cell cells (KBlob (SA CUR0 0) WLEN 1))%bool then
        match named_at cells (curE i) with Some (_, _, lo, hi) => step_chk Si lo hi okf | None => false end
      else false
  end.
(* [comment removed for export] *)
Definition nstc (cells : list kentry) : option expr := CAX.cell_at cells PE 210 1.

(* [comment removed for export] *)
Definition szc (c : CC.cutpoint) : expr := size_of (CC.cp_know c).
Definition szok (c : CC.cutpoint) : bool := (isSome (CAX.cell_at (CC.cp_know c) PE 232 8) && APC.expr_vars_lt (CC.cp_nx c) (szc c))%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition goto_common (i : nat) (c : CC.cutpoint) (s : CC.subst) : bool :=
  (expr_eqb (CC.slook s 50) FLE && expr_eqb (CC.slook s 55) FE && CBA.regions_eqb (CC.cp_F c) (cpf_of_kind (kind_of i)) && negb (Nat.eqb i 0))%bool.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition jtgt (s : CC.subst) (j : nat) : expr := CC.esubstL GT.NF s (jrem j).
Definition goto_decl_chk (i j : nat) (ps : SR.post_spec) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in
  match kind_of i, cut_states j with
  | KSm, Some Sj => match CX.range3 cells NST0 with
                   | Some (cn, cn') => (Z.eqb cn cn' && forallb (fun k => existsb (Z.eqb k) Sj) (entry_states cn) && rng_is cells (APC.esub WLEN (jtgt s j)) 0)%bool
                   | None => false end
  | KDecl, Some Sj => content_chk i cells (APC.esub (jrem i) (jtgt s j)) (fun k => existsb (Z.eqb k) Sj)
  | KDecl, None => isSome (cut_states i)          (* [comment removed for export] *)
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition cur_chk (cells : list kentry) (q : expr) : bool :=
  (prove cells (KRange (APC.esub q CUR0) 0 16384) && prove cells (KRange (APC.esub WEND q) 0 16384))%bool.
(* [comment removed for export] *)
Definition exit_exh (cells : list kentry) (q sz : expr) (cn0 : Z) : bool :=
  match nstc cells with
  | Some (ELit cn) => (Z.eqb cn cn0 && Z.leb 0 cn && Z.leb cn 7 && prove cells (KRange (APC.esub WEND q) 0 0) && prove cells (KRange (APC.esub q CUR0) 0 16384)
                      && CC.has_cell cells (KWord (SA PE 211) 1 (ELit 1)) && prove cells (KRange (APC.esub BX sz) 0 67108864))%bool
  | _ => false
  end.
(* [comment removed for export] *)
Definition nst_rng (cells : list kentry) : bool :=
  match nstc cells with Some (ELit z) => (Z.leb 0 z && Z.leb z 7)%bool | Some e => prove cells (KRange e 0 7) | None => false end.
Definition exit_err (cells : list kentry) (q : expr) : bool :=
  (nst_rng cells && CC.has_cell cells (KWord (SA PE 211) 1 (ELit 0)) && cur_chk cells q && prove cells (KRange (APC.esub BX (APC.eadd SIZE0 (APC.esub WEND q))) 0 67108864))%bool.
Definition goto_retx_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in let q := CC.slook s 78 in
  match kind_of i with
  | KDecl => (* [comment removed for export] *)
      match cut_states i, nstc cells with
      | Some Si, Some (ELit cn) => (Z.leb 0 cn && Z.leb cn 7 && forallb (nst_ok cn) Si && expr_eqb q CUR0 && prove cells (KRange WLEN 0 0)
                                    && CC.has_cell cells (KWord (SA PE 211) 1 (ELit 1)))%bool
      | _, _ => false end
  | KAppr => (szok c && prove cells (KRange (jrem i) 0 0) && match nstc (CC.cp_know c) with Some (ELit cn0) => exit_exh cells q (szc c) cn0 | _ => false end)%bool
  | KEnd => expr_eqb q (curE i)
  | KSetec => exit_err cells q
  | _ => false
  end.

(* [comment removed for export] *)
Definition call_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (pc : Z) : bool :=
  let cells := SR.ps_cells ps in
  match ret_of i k with
  | None => false
  | Some (j, cj) =>
    (Z.eqb (SR.ps_pc ps) pc && CBA.regions_eqb (CC.cp_F c) (cpf_of_kind (kind_of i)) && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
     && Bool.eqb (minus_fam i) (minus_fam j)) &&
    if Z.eqb pc PC_SM then
       (Nat.eqb i 0 && Nat.eqb j 48
        && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 (nth 0 G.BLS []) [] [] (List.filter (sm_ok ps) (CC.cp_know cj)) None c ps cj (nth 0 G.BLS []) [] (nth j G.BLS []) (nth j FFS []) with
           | Some ci => Nat.eqb (CH2.ci_nx ci) 50 && Z.eqb (CH2.ci_csp ci) (-160) | None => false end)
    else if Z.eqb pc PC_ERRH then
       (kind_eqb (kind_of i) KDecl && kind_eqb (kind_of j) KErrh && callee ps i j c cj 16 0 (nth i G.BLS []) [] NEWS_F None
        && CC.has_cell cells (KWord (SA PE 211) 1 (ELit 1)) && CC.has_cell cells (KWord (SA EE 0) 4 (ELit 0))
        && match reg_of ps 11 with                                    (* [comment removed for export] *)
           | EAlu Instr.ALU_ADD b (ELit k) =>
               expr_eqb b FE && Z.eqb (k mod 16) 0 && Z.leb 32 k && Z.leb k 112
               && match CAX.cell_at cells FE k 4 with Some (ELit v) => Z.leb 0 v && Z.ltb v 2147483648 | _ => false end
               && CC.has_cell cells (KWord (SA (CHA.SRL3 FE) (SBz + k / 8)) 1 (ELit 4))
           | _ => false end)
    else if Z.eqb pc PC_SETEC then
       (kind_eqb (kind_of i) KErrh && kind_eqb (kind_of j) KSetec && callee ps i j c cj 1024 0 (nth i G.BLS []) SETEC_W NEWS_F None && expr_eqb (reg_of ps 10) EE
        && match reg_of ps 11 with ELit z => (Z.leb 1 z && Z.leb z 31)%bool | _ => false end)
    else if Z.eqb pc PC_APPR then
       (kind_eqb (kind_of i) KDecl && kind_eqb (kind_of j) KAppr
        && callee ps i j c cj 4880 2 (tl (nth i G.BLS [])) STR_W (NEWS_F ++ STR_NEWS (gof ps i c cj 4880 2) (APC.eadd (size_of cells) (APC.esub (reg_of ps 12) (reg_of ps 11)))) None
        && expr_eqb (reg_of ps 10) (EAlu Instr.ALU_ADD PE (ELit 224)) && expr_eqb (reg_of ps 11) CUR0 && expr_eqb (reg_of ps 12) (curE i) && expr_eqb (size_of cells) SIZE0
        && CC.has_cell cells (KWord (SA PE 211) 1 (ELit 1)) && CC.has_cell cells (KWord (SA EE 0) 4 (ELit 0)) && CC.has_cell cells (KBlob (SA CUR0 0) WLEN 1)
        && prove cells (KRange (APC.esub BX (APC.eadd SIZE0 (APC.esub (curE i) CUR0))) 0 67108864)
        && szok cj && expr_eqb (szc cj) (APC.eadd SIZE0 (APC.esub (curE i) CUR0))
        && match nstc cells, nstc (CC.cp_know cj) with
           | Some (ELit cn), Some (ELit cn') => (Z.eqb cn cn' && Z.leb 0 cn && Z.leb cn 7 && content_chk i cells (APC.esub (curE i) (curE i)) (nst_ok cn))%bool      (* [comment removed for export] *)
           | Some (EVar v), Some (EVar v') => (Nat.eqb v 42 && Nat.eqb v' 42 && content_chk i cells (APC.esub (curE i) (curE i)) final_ok)%bool                      (* [comment removed for export] *)
           | _, _ => false
           end)
    else if (Z.eqb pc PC_ENDI || Z.eqb pc PC_ENDF) then
       (kind_eqb (kind_of i) KAppr && kind_eqb (kind_of j) KEnd
        && callee ps i j c cj 16544 5 [] ((if Z.eqb pc PC_ENDI then END_W else ENDE_W) ++ WENC) (NEWS_F ++ END_NEWS (gof ps i c cj 16544 5)) None      (* [comment removed for export] *)
        && expr_eqb (reg_of ps 10) PE && expr_eqb (reg_of ps 11) VE && expr_eqb (reg_of ps 12) EE
        && match nstc (CC.cp_know c) with Some (EVar v) => Nat.eqb v 42 | _ => false end          (* [comment removed for export] *)
        && CC.has_cell cells (KWord (SA PE 211) 1 (ELit 1)) && CC.has_cell cells (KWord (SA EE 0) 4 (ELit 0)) && CC.has_cell cells (KWord (SA PE 210) 1 NST0)
        && szok c && expr_eqb (size_of cells) (szc c) && prove cells (KRange (APC.esub (curE i) CUR0) 0 16384) && prove cells (KRange (APC.esub WEND (curE i)) 1 16384)
        && prove cells (KRange (APC.esub BX (APC.eadd (szc c) (APC.esub WEND (curE i)))) 0 67108864)      (* [comment removed for export] *)
        && Bool.eqb (minus_fam i) false)
    else false
  end%bool.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => goto_common i c s && Nat.ltb j NCUT && ((kind_eqb (kind_of j) KDecl && goto_decl_chk i j ps s) || (kind_eqb (kind_of j) KRetx && goto_retx_chk i c ps s))
  | CC.TOther pc =>
      if Z.eqb pc RETPC then (kind_eqb (kind_of i) KRetx && CBA.regions_eqb (CC.cp_F c) CPF_X && CBA.exit_base_chk GT.NF RETPC c ps && expr_eqb (reg_of ps 10) (EVar 78)
                               && CC.has_cell (SR.ps_cells ps) (KWord (SA FLE 0) 1 (ELit 0)))
      else if (Z.eqb pc PC_SM || Z.eqb pc PC_ERRH || Z.eqb pc PC_SETEC || Z.eqb pc PC_APPR || Z.eqb pc PC_ENDI || Z.eqb pc PC_ENDF) then call_chk i c k ps pc
      else match CSLR.find_row ROWS i (SR.ps_pc ps) with
           | Some r => (kind_eqb (kind_of i) KDecl && kind_eqb (kind_of (CSLR.r_j r)) KDecl && Bool.eqb (minus_fam i) (minus_fam (CSLR.r_j r))
                        && match cut_states i, cut_states (CSLR.r_j r) with Some Si, Some Sj => forallb (fun k => existsb (Z.eqb k) Sj) Si | _, _ => false end
                        && CSLR.row_chk GT.NF G.HDECL G.CPS G.BLS FFS CPF_N SBz (mvar i) CUR0 WEND 134217728 KZB TLO TG KZT i c ps r)
           | None => false
           end
  end%bool.
Definition tagc (t : CC.tag) : Z := match t with CC.TGoto j _ => 1000 + Z.of_nat j | CC.TOther pc => pc end.
(* [comment removed for export] *)
Definition fails (lo n : nat) : list (nat * nat * Z) :=
  flat_map (fun i => let c := nth i G.CPS CA.dummy_cp in let tg := nth i G.TAGS [] in
     flat_map (fun k => let ps := nth k (CC.cp_PSS c) (SR.PS 0 [] [] []) in let t := nth k tg (CC.TOther 0) in if leaf_chk i c k ps t then [] else [(i, k, tagc t)]) (seq 0 (length tg))) (seq lo n).

(* [comment removed for export] *)
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
Lemma leaves_rng_sound : forall lo n, leaves_rng lo n = true ->
  forall i c k ps t, (lo <= i < lo + n)%nat -> CH2.is_leaf G.CPS G.TAGS i c k ps t -> leaf_chk i c k ps t = true.
Proof.
  intros lo n H i c k ps t Hi (tags & Hc & Htg & Hps & Ht). unfold leaves_rng in H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; exact Hi)). rewrite Hc, Htg in H. rewrite forallb_forall in H.
  assert (Hk : (k < length tags)%nat) by (apply nth_error_Some; rewrite Ht; discriminate).
  specialize (H k ltac:(apply in_seq; split; [apply Nat.le_0_l | exact Hk])). rewrite Hps, Ht in H. exact H.
Qed.
(* [comment removed for export] *)
Lemma blv_all : forallb (fun i => CH2.blocks_vars_lt (CC.cp_nx (nth i G.CPS CA.dummy_cp)) (nth i G.BLS [])) (seq 0 74) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma len_cps : length G.CPS = 74%nat. Proof. vm_compute. reflexivity. Qed.
Lemma retx_chk : CHA.retire_chk GT.NF G.HDECL (nth 47 G.CPS CA.dummy_cp) (nth 47 G.BLS []) (nth 47 FFS []) = Some FLE.
Proof. vm_compute. reflexivity. Qed.
Lemma retx_nth : nth_error G.CPS 47 = Some (nth 47 G.CPS CA.dummy_cp).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition tmpl_chk (i : nat) : bool :=
  let c := nth i G.CPS CA.dummy_cp in let cells := CC.cp_know c in
  match kind_of i with
  | KDecl => (CC.has_cell cells (KWord (SA PE 211) 1 (ELit 1)) && CC.has_cell cells (KWord (SA EE 0) 4 (ELit 0)) && CC.has_cell cells (KBlob (SA CUR0 0) WLEN 1)
              && expr_eqb (szc c) SIZE0 && (minus_fam i || isSome (CX.range3 cells JV)))%bool
  | _ => true
  end.
Lemma tmpl_all : forallb tmpl_chk (seq 0 74) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cpf_all : forallb (fun c => cpf_ok (CC.cp_F c)) G.CPS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sites : CSLR.sites_ok RSEGS ROWS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End PNA.
