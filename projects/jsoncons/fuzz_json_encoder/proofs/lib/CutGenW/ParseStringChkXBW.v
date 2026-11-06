(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutShA CutShB CutShC.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_ps_xbothw_T Cut_ps_xbothw_D Cut_ps_xbothw.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsKitA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PSA.
(* [comment removed for export] *)
Module G.
Definition CPS := Cut_ps_xbothw_D.CPS. Definition BLS := Cut_ps_xbothw_D.BLS. Definition TAGS := Cut_ps_xbothw_D.TAGS. Definition RETS := Cut_ps_xbothw_D.RETS.
Definition HDECL := Cut_ps_xbothw_T.HDECL. Definition cp0 := Cut_ps_xbothw_D.cp0.
Definition plans := Cut_ps_xbothw.plans. Definition tags_ok := Cut_ps_xbothw.tags_ok. Definition NF_le := Cut_ps_xbothw.NF_le.
End G.
Module GT.
Definition NF := Cut_ps_xbothw_T.NF. Definition HDECL := Cut_ps_xbothw_T.HDECL. Definition SCELLS := Cut_ps_xbothw_T.SCELLS. Definition GLO := Cut_ps_xbothw_T.GLO. Definition GHI := Cut_ps_xbothw_T.GHI.
Definition t0 := Cut_ps_xbothw_T.t0.
End GT.
Abbreviation RSEGS := Pm5PlanKit.RSEGS.
Definition PC_SM : Z := 420020. Definition PC_ATC : Z := 922968. Definition PC_CONVERT : Z := 923544. Definition PC_PUSHB : Z := 1056004. Definition PC_APPEND : Z := 1055420.
Definition PC_SETEC : Z := 842884. Definition PC_ESV : Z := 919748. Definition PC_ERRH : Z := 852452. Definition RETPC : Z := 900692.
Definition SBz : Z := 2147450880. Definition GD : Z := 6946368. Definition AXT : Z := 7084256. Definition ISH2 : Z := 2147630410. Definition VT_VISITOR : Z := 1435200.
Definition PE := EVar 10. Definition CUR0 := EVar 11. Definition VE := EVar 12. Definition EE := EVar 13.
Definition WLEN := EVar 32. Definition BX := EVar 33. Definition SBX := EVar 37. Definition SLEN := EVar 38. Definition SCAP := EVar 39. Definition CH := EVar 47. Definition FLE := EVar 50. Definition JV := EVar 51. Definition FE := EVar 55.
Definition WEND : expr := EAlu Instr.ALU_ADD CUR0 WLEN.
Definition CUR : expr := EAlu Instr.ALU_ADD CUR0 (EAlu Instr.ALU_ADD WLEN (EMd Instr.M_MUL (ELit (-1)) JV)).     (* [comment removed for export] *)
Definition NCUT : nat := 79.

(* [comment removed for export] *)
Inductive kind : Set := KEntry | KDecl | KRetx | KSm | KPushb | KAppend | KConvert | KAtc | KErrh | KSetec | KEsv.
Definition kind_eqb (a b : kind) : bool :=
  match a, b with KEntry, KEntry | KDecl, KDecl | KRetx, KRetx | KSm, KSm | KPushb, KPushb | KAppend, KAppend | KConvert, KConvert | KAtc, KAtc | KErrh, KErrh | KSetec, KSetec | KEsv, KEsv => true | _, _ => false end.
Lemma kind_eqb_eq : forall a b, kind_eqb a b = true -> a = b. Proof. intros [] [] H; try discriminate; reflexivity. Qed.
Definition ret_of_kind (pc : Z) : kind :=
  if Z.eqb pc PC_SM then KSm else if Z.eqb pc PC_PUSHB then KPushb else if Z.eqb pc PC_APPEND then KAppend else if Z.eqb pc PC_CONVERT then KConvert
  else if Z.eqb pc PC_ATC then KAtc else if Z.eqb pc PC_ERRH then KErrh else if Z.eqb pc PC_SETEC then KSetec else KEsv.
Definition RETXI : nat := 28.      (* [comment removed for export] *)
Definition kind_of (j : nat) : kind :=
  if Nat.eqb j 0 then KEntry else if Nat.eqb j RETXI then KRetx else
  match find (fun r : nat * nat * nat * Z => let '(j', _, _, _) := r in Nat.eqb j j') G.RETS with
  | Some (_, _, _, pc) => ret_of_kind pc
  | None => KDecl
  end.
(* [comment removed for export] *)
Definition phase0 (k : kind) : bool := match k with KAtc | KSetec | KEsv | KRetx => false | _ => true end.
(* [comment removed for export] *)
Definition ecv_of (c : CC.cutpoint) : option nat := match CAX.cell_at (CC.cp_know c) EE 0 4 with Some (EVar g) => Some g | _ => None end.
Definition ecv (i : nat) : nat := match ecv_of (nth i G.CPS CA.dummy_cp) with Some g => g | None => 0%nat end.

(* [comment removed for export] *)
Definition FR : expr * Z * Z := (FE, 1, -288).
Definition FFS : list (list (expr * Z * Z)) := [] :: repeat [FR] 78.
Definition blk0 (i : nat) : expr * expr := hd (ELit 0, ELit 0) (nth i G.BLS []).
Definition blk1 (i : nat) : expr * expr := hd (ELit 0, ELit 0) (tl (nth i G.BLS [])).

(* [comment removed for export] *)
Definition SIDI : CC.subst := map (fun k => (k, EVar k)) (seq 50 32).
(* [comment removed for export] *)
Definition SIDU : CC.subst := map (fun k => (k, if Nat.eqb k 67 then EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL CUR (ELit 3)) (ELit SBz) else if Nat.eqb k 68 then ELit 0 else EVar k)) (seq 50 32).
Definition KZB : kentry := CSLR.KZB SBz CH (ELit 2048).
Definition KZT : kentry := CSLR.KZT 0 SBz.   (* [comment removed for export] *)
Definition ROWS : list CSLR.row :=
  [CSLR.ROW 1 897724 2 SIDI 10 10 CUR 60 58 false; CSLR.ROW 3 897880 4 SIDI 10 10 CUR 56 54 false; CSLR.ROW 5 898064 6 SIDI 13 11 CUR 52 50 false;
   CSLR.ROW 7 898232 8 SIDI 13 11 CUR 48 46 false; CSLR.ROW 9 898400 10 SIDI 13 11 CUR 44 42 false; CSLR.ROW 11 898556 12 SIDI 10 10 CUR 40 38 false;
   CSLR.ROW 13 898668 14 SIDI 10 10 CUR 36 34 false; CSLR.ROW 15 898748 16 SIDI 10 10 CUR 32 30 false; CSLR.ROW 17 898908 18 SIDU 13 11 CUR 28 26 false;
   CSLR.ROW 19 899060 20 SIDU 13 11 CUR 24 22 false; CSLR.ROW 21 899212 22 SIDU 13 11 CUR 20 18 false; CSLR.ROW 26 899504 27 SIDI 10 10 CUR 12 10 false].
(* [comment removed for export] *)
Definition F0 : list SGP.region := [(EVar 2, -16896, ELit 16896); (PE, 148, ELit 8); (PE, 168, ELit 8); (PE, 209, ELit 1); (PE, 220, ELit 1)].
Definition FRM3 : list SGP.region := [(FE, 0, ELit 24); (FE, 32, ELit 88); (CHA.SRL3 FE, SBz, ELit 16)].
Definition FLR : SGP.region := (FLE, 0, ELit 1).
Definition MORE : SGP.region := (PE, 211, ELit 1).
Definition CPF_N : list SGP.region := F0 ++ FRM3.                   (* [comment removed for export] *)
Definition CPF_NM : list SGP.region := F0 ++ FRM3 ++ [MORE].        (* [comment removed for export] *)
Definition CPF_MM : list SGP.region := F0 ++ FRM3 ++ [MORE; MORE].  (* [comment removed for export] *)
Definition CPF_E : list SGP.region := [(EVar 2, -16896, ELit 16896); (FE, 0, ELit 24); (FE, 32, ELit 88); (CHA.SRL3 FE, SBz, ELit 16)].   (* [comment removed for export] *)
Definition CPF_X : list SGP.region := [(EVar 2, -16896, ELit 16896); (FE, 0, ELit 24); (CHA.SRL3 FE, SBz, ELit 16); FLR].              (* [comment removed for export] *)
Definition cpf_of_kind (k : kind) : list SGP.region :=
  match k with KEntry => F0 | KRetx => CPF_X | KErrh => CPF_NM | KSetec => CPF_MM | KEsv => CPF_E | _ => CPF_N end.
(* [comment removed for export] *)
Definition UREGS : list SGP.region := [(EVar 2, -16896, ELit 16896); (PE, 148, ELit 8); (PE, 168, ELit 8); (PE, 209, ELit 1); (PE, 211, ELit 1); (PE, 220, ELit 1);
                                       (FE, 0, ELit 24); (FE, 32, ELit 88); (CHA.SRL3 FE, SBz, ELit 16); FLR].
Definition region_eqb (x y : SGP.region) : bool := (expr_eqb (fst (fst x)) (fst (fst y)) && Z.eqb (snd (fst x)) (snd (fst y)) && expr_eqb (snd x) (snd y))%bool.
Definition cpf_ok (F : list SGP.region) : bool := forallb (fun r => existsb (region_eqb r) UREGS) F.

Definition has := CC.has_cell.
Definition STAT : list kentry := [KImg 1459384 1463120; KWord (SA (ELit 0) 1497016) 8 (ELit SBz); KWord (SA (ELit 0) 1497024) 4 (ELit 1)].
Definition ISHL : list kentry := [KZero (SA (ELit 0) ISH2) (ELit 1)].
Definition FLAG : list kentry := [KWord (SA FE 120) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition NEWS_F : list kentry := STAT ++ ISHL ++ FLAG.
Definition SETEC_W : list SGP.region := [(EE, 0, ELit 16); (ELit 0, GD, ELit 2); (ELit 0, AXT, ELit 544)].
Definition ATC_W : list SGP.region := MORE :: SETEC_W.
Definition STR_W : list SGP.region := [(PE, 224, ELit 24)].
Definition ESV_W : list SGP.region := [(PE, 0, ELit 272); (EE, 0, ELit 16); (ELit 0, GD, ELit 2); (ELit 0, AXT, ELit 544)].
Definition S2E := EVar 49.          (* [comment removed for export] *)
Definition LITLO : Z := 6946376.    (* [comment removed for export] *)
Definition WENC : list SGP.region := [(VE, 264, ELit 40); (VE, 400, ELit 4); (S2E, 0, ELit 24); (ELit 0, LITLO, ELit 72)].   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ATC_NEWS (g : nat) : list kentry := [KWord (SA EE 0) 4 (EVar g); KRange (EVar g) 0 31].
(* [comment removed for export] *)
Definition size_of (cells : list kentry) : expr := match CAX.cell_at cells PE 232 8 with Some e => e | None => ELit 0 end.
Definition STR_NEWS (g : nat) (sz : expr) : list kentry :=
  let cap := APC.escale 2 (EVar (g + 1)%nat) in
  [KWord (SA PE 224) 8 (APC.eaddz cap 1); KWord (SA PE 232) 8 sz; KWord (SA PE 240) 8 (EVar g);
   KRange (EVar (g + 1)%nat) 132 67108864; KRange (APC.esub (APC.eaddz cap (-1)) sz) 0 140737488355328; KAlign cap 8].
Definition CONV_NEWS (g : nat) (cells : list kentry) : list kentry :=
  STR_NEWS g (EVar (g + 2)%nat) ++ [KRange (EVar (g + 2)%nat) 0 67108863; KRange (APC.esub (EVar (g + 2)%nat) (size_of cells)) 0 4;
                                    KRange (APC.esub (APC.eaddz BX 1) (APC.eadd (EVar (g + 2)%nat) JV)) 0 67108864].
Definition ESV_NEWS (g : nat) : list kentry :=
  [KWord (SA EE 0) 4 (EVar g); KRange (EVar g) 0 31; KWord (SA PE 240) 8 (EVar (g + 1)%nat); KWord (SA PE 224) 8 (APC.eaddz (APC.escale 2 (EVar (g + 2)%nat)) 1);
   KWord (SA PE 248) 8 (EVar (g + 3)%nat); KWord (SA PE 264) 8 (APC.eadd (EVar (g + 3)%nat) (EVar (g + 4)%nat));
   KWord (SA PE 148) 4 (EVar (g + 5)%nat); KWord (SA PE 152) 4 (EVar (g + 6)%nat)].      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SMUSER : list kentry := [KDisj (SA FE 0) (ELit 128) (SA CUR0 0) WLEN; KDisj (SA FLE 0) (ELit 1) (SA CUR0 0) WLEN].
Definition sm_ok (ps : SR.post_spec) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok 7094272 G.HDECL (SR.ps_cells ps) 50 (nth 0 G.BLS []) [] 1 55 50 X || CC.has_cell (ISHL ++ SMUSER) X)%bool.
(* [comment removed for export] *)
Definition callee (ps : SR.post_spec) (i j : nat) (c cj : CC.cutpoint) (scr : Z) (ng : nat) (BLk : CA.blocks) (wregs : list SGP.region) (news : list kentry) (a0x : option expr) : bool :=
  match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr ng BLk (nth i FFS []) wregs news a0x c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
  | Some ci => Z.eqb (CH2.ci_csp ci) (-288)
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
Definition szc (c : CC.cutpoint) : expr := size_of (CC.cp_know c).
Definition szok (c : CC.cutpoint) : bool := (isSome (CAX.cell_at (CC.cp_know c) PE 232 8) && APC.expr_vars_lt (CC.cp_nx c) (szc c))%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition goto_common (i : nat) (c : CC.cutpoint) (s : CC.subst) : bool :=
  (expr_eqb (CC.slook s 50) FLE && expr_eqb (CC.slook s 55) FE && CBA.regions_eqb (CC.cp_F c) (cpf_of_kind (kind_of i)) && negb (Nat.eqb i 0))%bool.
(* [comment removed for export] *)
Definition goto_decl_chk (i : nat) (ps : SR.post_spec) : bool :=
  match kind_of i with
  | KSm | KDecl | KPushb | KAppend | KConvert => true
  | KAtc => prove (SR.ps_cells ps) (KRange (EVar (ecv i)) 0 0)
  | _ => false
  end.
(* [comment removed for export] *)
Definition ESC_NEED : list Z := [0; 0; 0; 1; 2; 3; 0; 0; 0; 1; 2; 3].   (* [comment removed for export] *)
Definition cur_chk (cells : list kentry) (q : expr) : bool :=
  (prove cells (KRange (APC.esub q CUR0) 0 16384) && prove cells (KRange (APC.esub WEND q) 0 16384))%bool.
Definition progress_chk (cells : list kentry) (q : expr) : bool :=
  (prove cells (KRange (APC.esub q CUR0) 1 16384) || prove cells (KRange (APC.esub WEND q) 0 0))%bool.
Definition bound_chk (cells : list kentry) (q sz : expr) (need : Z) : bool :=
  prove cells (KRange (APC.esub BX (APC.eaddz (APC.eadd sz (APC.esub WEND q)) need)) 0 67108864).
(* [comment removed for export] *)
Definition exit_ok0 (cells : list kentry) (q sz : expr) : bool :=
  match CAX.cell_at cells PE 209 1 with
  | Some (ELit z) => (Z.leb 0 z && Z.leb z 11 && cur_chk cells q && progress_chk cells q && bound_chk cells q sz (nth (Z.to_nat z) ESC_NEED 0))%bool
  | _ => false
  end.
(* [comment removed for export] *)
Definition sst_rng (cells : list kentry) : bool :=
  match CAX.cell_at cells PE 209 1 with Some (ELit z) => (Z.leb 0 z && Z.leb z 11)%bool | Some e => prove cells (KRange e 0 11) | None => false end.
Definition exit_err (cells : list kentry) (q sz : expr) : bool := (sst_rng cells && cur_chk cells q && bound_chk cells q sz 0)%bool.
Definition goto_retx_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in let q := CC.slook s 78 in let sz := szc c in
  (szok c &&
  match kind_of i with
  | KSm | KDecl | KPushb | KAppend | KConvert => exit_ok0 cells q sz
  | KAtc => ((prove cells (KRange (EVar (ecv i)) 0 0) && exit_ok0 cells q sz) || (prove cells (KRange (EVar (ecv i)) 1 31) && exit_err cells q sz))%bool
  | KSetec => (CC.has_cell cells (KWord (SA PE 211) 1 (ELit 0)) && exit_err cells q sz)%bool
  | _ => false
  end)%bool
  || match kind_of i with
     | KEsv => ((expr_eqb q (EAlu Instr.ALU_ADD CUR (ELit 1)) && prove cells (KRange (EVar (ecv i)) 0 0)) || (expr_eqb q CUR && prove cells (KRange (EVar (ecv i)) 1 31)))%bool
     | _ => false
     end.

(* [comment removed for export] *)
Definition call_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (pc : Z) : bool :=
  let cells := SR.ps_cells ps in
  match ret_of i k with
  | None => false
  | Some (j, cj) =>
    (Z.eqb (SR.ps_pc ps) pc && CBA.regions_eqb (CC.cp_F c) (cpf_of_kind (kind_of i)) && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])) &&
    if Z.eqb pc PC_SM then
       (Nat.eqb i 0 && Nat.eqb j 29
        && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 (nth 0 G.BLS []) [] [] (List.filter (sm_ok ps) (CC.cp_know cj)) None c ps cj (nth 0 G.BLS []) [] (nth j G.BLS []) (nth j FFS []) with
           | Some ci => Nat.eqb (CH2.ci_nx ci) 50 && Z.eqb (CH2.ci_csp ci) (-288) | None => false end)
    else if Z.eqb pc PC_ERRH then
       (phase0 (kind_of i) && negb (Nat.eqb i 0) && kind_eqb (kind_of j) KErrh && callee ps i j c cj 16 0 (nth i G.BLS []) [] NEWS_F (Some (ELit 0))
        && match reg_of ps 11 with                                    (* [comment removed for export] *)
           | EAlu Instr.ALU_ADD b (ELit k) =>
               expr_eqb b FE && Z.eqb (k mod 16) 0 && Z.leb 32 k && Z.leb k 112
               && match CAX.cell_at cells FE k 4 with Some (ELit v) => Z.leb 0 v && Z.ltb v 2147483648 && negb (Z.eqb v 24) | _ => false end
               && CC.has_cell cells (KWord (SA (CHA.SRL3 FE) (SBz + k / 8)) 1 (ELit 4))
           | _ => false end)
    else if Z.eqb pc PC_SETEC then
       (kind_eqb (kind_of i) KErrh && kind_eqb (kind_of j) KSetec && callee ps i j c cj 1024 0 (nth i G.BLS []) SETEC_W NEWS_F None && expr_eqb (reg_of ps 10) EE
        && match reg_of ps 11 with ELit z => (Z.leb 1 z && Z.leb z 31)%bool | _ => false end)
    else if Z.eqb pc PC_ATC then
       (kind_eqb (kind_of i) KDecl && kind_eqb (kind_of j) KAtc && callee ps i j c cj 1120 1 (nth i G.BLS []) ATC_W (NEWS_F ++ ATC_NEWS (gof ps i c cj 1120 1)) None
        && Nat.eqb (ecv j) (gof ps i c cj 1120 1) && expr_eqb (reg_of ps 10) PE && expr_eqb (reg_of ps 13) EE
        && prove cells (KRange (reg_of ps 12) 0 255))      (* [comment removed for export] *)
    else if Z.eqb pc PC_PUSHB then
       (kind_eqb (kind_of i) KDecl && kind_eqb (kind_of j) KPushb
        && callee ps i j c cj 4368 2 (tl (nth i G.BLS [])) STR_W (NEWS_F ++ STR_NEWS (gof ps i c cj 4368 2) (APC.eaddz (size_of cells) 1)) None
        && expr_eqb (reg_of ps 10) (EAlu Instr.ALU_ADD PE (ELit 224)) && match reg_of ps 11 with ELit z => (Z.leb 0 z && Z.ltb z 256)%bool | _ => false end
        && szok c && prove cells (KRange (APC.esub BX (APC.eaddz (szc c) 1)) 0 67108864))
    else if Z.eqb pc PC_APPEND then
       ((phase0 (kind_of i) && negb (Nat.eqb i 0)) && kind_eqb (kind_of j) KAppend
        && callee ps i j c cj 4368 2 (tl (nth i G.BLS [])) STR_W (NEWS_F ++ STR_NEWS (gof ps i c cj 4368 2) (APC.eadd (size_of cells) (reg_of ps 12))) None
        && expr_eqb (reg_of ps 10) (EAlu Instr.ALU_ADD PE (ELit 224))
        && cur_chk cells (reg_of ps 11) && prove cells (KRange (reg_of ps 12) 0 16384) && prove cells (KRange (APC.esub WEND (APC.eadd (reg_of ps 11) (reg_of ps 12))) 0 16384)
        && szok c && prove cells (KRange (APC.esub BX (APC.eadd (szc c) (reg_of ps 12))) 0 67108864))
    else if Z.eqb pc PC_CONVERT then
       (kind_eqb (kind_of i) KDecl && kind_eqb (kind_of j) KConvert
        && callee ps i j c cj 4496 3 (tl (nth i G.BLS [])) STR_W (NEWS_F ++ CONV_NEWS (gof ps i c cj 4496 3) cells) None
        && expr_eqb (reg_of ps 12) (EAlu Instr.ALU_ADD PE (ELit 224)) && expr_eqb (reg_of ps 11) (ELit 1) && expr_eqb (reg_of ps 13) (ELit 0)
        && (expr_eqb (reg_of ps 10) (EAlu Instr.ALU_ADD PE (ELit 148)) || (expr_eqb (reg_of ps 10) (EAlu Instr.ALU_ADD FE (ELit 112)) && CC.has_cell cells (KWord (SA (CHA.SRL3 FE) (SBz + 14)) 1 (ELit 4))))
        && match reg_of ps 10 with EAlu Instr.ALU_ADD b (ELit k) => isSome (CAX.cell_at cells b k 4) | _ => false end
        && szok c && prove cells (KRange (APC.esub BX (APC.eaddz (APC.eadd (szc c) JV) 3)) 0 67108864))
    else if Z.eqb pc PC_ESV then
       ((phase0 (kind_of i) && negb (Nat.eqb i 0)) && kind_eqb (kind_of j) KEsv
        && callee ps i j c cj 16544 7 [] (ESV_W ++ WENC) (NEWS_F ++ ESV_NEWS (gof ps i c cj 16544 7)) None      (* [comment removed for export] *)
        && Nat.eqb (ecv j) (gof ps i c cj 16544 7)
        && expr_eqb (reg_of ps 10) PE && expr_eqb (reg_of ps 13) VE && expr_eqb (reg_of ps 14) EE
        && ((expr_eqb (reg_of ps 11) (fst (blk0 i)) && expr_eqb (reg_of ps 12) (size_of cells))      (* [comment removed for export] *)
            || (cur_chk cells (reg_of ps 11) && prove cells (KRange (reg_of ps 12) 0 16384) && prove cells (KRange (APC.esub WEND (APC.eadd (reg_of ps 11) (reg_of ps 12))) 0 16384)))   (* [comment removed for export] *)
        && szok c && prove cells (KRange (APC.esub BX (APC.eadd (szc c) (APC.esub WEND CUR))) 0 67108864)      (* [comment removed for export] *)
        && CC.has_cell cells (KWord (SA PE 209) 1 (EVar 60)) && prove cells (KRange (EVar 60) 0 11) && prove cells (KRange (APC.esub CUR CUR0) 0 16384) && prove cells (KRange (APC.esub WEND CUR) 1 16384))
    else false
  end%bool.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => goto_common i c s && Nat.ltb j NCUT && ((kind_eqb (kind_of j) KDecl && goto_decl_chk i ps) || (kind_eqb (kind_of j) KRetx && goto_retx_chk i c ps s))
  | CC.TOther pc =>
      if Z.eqb pc RETPC then (kind_eqb (kind_of i) KRetx && CBA.regions_eqb (CC.cp_F c) CPF_X && CBA.exit_base_chk GT.NF RETPC c ps && expr_eqb (reg_of ps 10) (EVar 78)
                               && CC.has_cell (SR.ps_cells ps) (KWord (SA FLE 0) 1 (ELit 0)))
      else if (Z.eqb pc PC_SM || Z.eqb pc PC_ERRH || Z.eqb pc PC_SETEC || Z.eqb pc PC_ATC || Z.eqb pc PC_PUSHB || Z.eqb pc PC_APPEND || Z.eqb pc PC_CONVERT || Z.eqb pc PC_ESV) then call_chk i c k ps pc
      else match CSLR.find_row ROWS i (SR.ps_pc ps) with
           | Some r => (kind_eqb (kind_of i) KDecl && CSLR.row_chk GT.NF G.HDECL G.CPS G.BLS FFS CPF_N SBz 51 CUR0 WEND 134217728 KZB 0 0 KZT i c ps r)
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
(* [comment removed for export] *)
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
Lemma blv_all : forallb (fun i => CH2.blocks_vars_lt (CC.cp_nx (nth i G.CPS CA.dummy_cp)) (nth i G.BLS [])) (seq 0 79) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ecv_lt : forallb (fun i => match kind_of i with KAtc | KEsv => Nat.ltb (ecv i) (CC.cp_nx (nth i G.CPS CA.dummy_cp)) | _ => true end) (seq 0 79) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma len_cps : length G.CPS = 79%nat. Proof. vm_compute. reflexivity. Qed.
Lemma retx_chk : CHA.retire_chk GT.NF G.HDECL (nth 28 G.CPS CA.dummy_cp) (nth 28 G.BLS []) (nth 28 FFS []) = Some FLE.
Proof. vm_compute. reflexivity. Qed.
Lemma retx_nth : nth_error G.CPS 28 = Some (nth 28 G.CPS CA.dummy_cp).
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
End PSA.
