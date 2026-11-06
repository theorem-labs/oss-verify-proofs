(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA PmLibDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutShA CutShB CutShC.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibSpecs PmEncSpecs PmLibSpecsX PmLibSpecsW PmRef RelLeaf.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_pn_xboth_T Cut_pn_xboth_D Cut_pn_xboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsKitA ParseNumberChkXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import SmallPtXBW ParseNumberKXBW.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PNCXAW.
Import PNA PNKW.
(* [comment removed for export] *)
Inductive wkind : Set := WEntry | WGo | WFin | WErr | WSm | WApp | WErrh | WSetEc | WEnd | WRetx | WNone.
Definition wkind_eqb (a b : wkind) : bool :=
  match a, b with WEntry, WEntry | WGo, WGo | WFin, WFin | WErr, WErr | WSm, WSm | WApp, WApp | WErrh, WErrh | WSetEc, WSetEc | WEnd, WEnd | WRetx, WRetx | WNone, WNone => true | _, _ => false end.
Lemma wkind_eqb_eq : forall a b, wkind_eqb a b = true -> a = b.
Proof. intros [] [] H; try reflexivity; discriminate H. Qed.
Definition WK (i : nat) : wkind :=
  match kind_of i with
  | KEntry => WEntry
  | KDecl => if Nat.leb i 29 then WGo else if Nat.leb i 33 then WFin else if Nat.leb i 38 then WErr else WGo      (* [comment removed for export] *)
  | KRetx => WRetx | KSm => WSm | KAppr => WApp | KErrh => WErrh | KSetec => WSetEc | KEnd => WEnd
  end.
Definition is_exh (i : nat) : bool := (Nat.leb 39 i && Nat.leb i 46)%bool.
(* [comment removed for export] *)
Definition NST (i : nat) : Z :=
  match cut_states i with
  | Some [k] => k
  | Some [1; 2] => 2
  | _ => match i with 34%nat => 3 | 35%nat => 1 | 36%nat => 0 | 37%nat => 5 | 38%nat => 6 | _ => -1 end
  end.
(* [comment removed for export] *)
Definition SRC (j : nat) : nat := match find (fun r : nat * nat * nat * Z => let '(j', _, _, _) := r in Nat.eqb j j') G.RETS with Some (_, i, _, _) => i | None => 0%nat end.
(* [comment removed for export] *)
Definition ERRC0 (i : nat) : Z := match i with 34%nat | 36%nat | 37%nat | 38%nat => 19 | 35%nat => 18 | _ => 0 end.
Definition ERRC (i : nat) : Z := match kind_of i with KErrh => ERRC0 (SRC i) | _ => ERRC0 i end.
Definition cutn (i : nat) : CC.cutpoint := nth i G.CPS CA.dummy_cp.
(* [comment removed for export] *)
Definition ECODE (j : nat) : Z :=
  match find (fun r : nat * nat * nat * Z => let '(j', _, _, _) := r in Nat.eqb j j') G.RETS with
  | Some (_, i, k, _) => match reg_of (nth k (CC.cp_PSS (cutn i)) (SR.PS 0 [] [] [])) 11 with ELit z => z | _ => -1 end
  | None => -1
  end.
(* [comment removed for export] *)
Definition NLIT (i : nat) : option Z := match nstc (CC.cp_know (cutn i)) with Some (ELit c) => Some c | _ => None end.

(* [comment removed for export] *)
Definition TABIMG : kentry := KImg 166136 166400.
Definition CLS (b : Z) : Z := match know_bytes_lit RSEGS [TABIMG] (ELit 0) (TAB + b) 1 with Some [t] => t | _ => -1 end.
Definition CLST : list Z := Eval vm_compute in map CLS (zseq 0 255).
Definition clsb (b : Z) : Z := nth (Z.to_nat b) CLST (-1).
(* [comment removed for export] *)
Definition tab_okb (v : nat) (b : Z) (X : kentry) : bool :=
  match X with KWord (SA (EVar v') o) 1 (ELit t) => (negb (Nat.eqb v' v && Z.eqb o TAB && Z.leb 0 t && Z.ltb t 256) || Z.eqb (clsb b) t)%bool | _ => true end.
Definition adm_tab (v : nat) (cells : list kentry) (lo : Z) (n : nat) (f : Z -> bool) : bool :=
  RLF.forall_b lo n (fun z => negb (RLF.byte_adm v cells z && forallb (tab_okb v z) cells) || f z)%bool.
(* [comment removed for export] *)
Lemma TABLE_ok : RLF.all_bytes (fun b => match know_bytes_lit RSEGS [TABIMG] (ELit 0) (TAB + b) 1 with Some [t] => Z.eqb t (clsb b) | _ => false end) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma table_read : forall E (M' : mem) b, 0 <= b <= 255 -> kentry_ok RSEGS E M' TABIMG ->
  exists t, rdn RSEGS M' (Z_to_bv 64 (TAB + b)) 1 = Some [t] /\ bv_unsigned t = clsb b.
Proof.
  intros E M' b Hb HK. pose proof (RLF.all_bytes_sound _ b TABLE_ok Hb) as X. cbv beta in X.
  destruct (know_bytes_lit RSEGS [TABIMG] (ELit 0) (TAB + b) 1) as [[|t [|? ?]]|] eqn:Hl; try discriminate X. apply Z.eqb_eq in X.
  assert (HK1 : know_ok RSEGS E M' [TABIMG]) by (constructor; [exact HK | constructor]).
  assert (Hfl : flat E (SA (ELit 0) (TAB + b)) (Z.of_nat 1)) by (unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; unfold TAB in *; lia).
  destruct (know_bytes_lit_sound RSEGS E M' _ (ELit 0) 1%nat (TAB + b) _ HK1 Hl Hfl) as (bs & Hr & Hm).
  rewrite (CL5.adenot_start E _ _ Hfl) in Hr. unfold estart in Hr. cbn [a_base a_off edenot] in Hr. rewrite (u64_of_Z 0), Z.add_0_l in Hr by lia.
  destruct bs as [|b0 [|? ?]]; try discriminate Hm. cbn in Hm. injection Hm as Hm. exists b0. split; [exact Hr | rewrite Hm; exact X].
Qed.
Lemma wle1 : forall x : word, word_to_le_bytes 1 x = [Z_to_bv 8 (bv_unsigned x)].
Proof. intros x. unfold word_to_le_bytes. cbn. f_equal. Qed.
Lemma tab_cells_sound : forall v cells E' (M' : mem) z, know_ok RSEGS E' M' cells -> CC.has_cell cells TABIMG = true ->
  CL5A.uv E' (EVar v) = z -> 0 <= z <= 255 -> forallb (tab_okb v z) cells = true.
Proof.
  intros v cells E' M' z HK HT Hz Hr. apply forallb_forall. intros X HX. pose proof (proj1 (Forall_forall _ _) HK X HX) as KX.
  destruct X as [a w e| | | | | | | | |]; cbn [tab_okb]; try reflexivity. destruct a as [ab ao]. destruct ab as [|v'| | | | | |]; try reflexivity.
  destruct w as [|[|w]]; try reflexivity. destruct e as [t| | | | | | |]; try reflexivity.
  destruct (Nat.eqb v' v && Z.eqb ao TAB && Z.leb 0 t && Z.ltb t 256)%bool eqn:G; [|reflexivity]. cbn [negb orb].
  apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2]. apply Nat.eqb_eq in G1. apply Z.eqb_eq in G2. apply Z.leb_le in G3. apply Z.ltb_lt in G4. subst v' ao.
  cbn [kentry_ok] in KX. destruct KX as (_ & Hfl & Hrd). rewrite (CL5.adenot_start E' _ _ Hfl) in Hrd. unfold estart in Hrd. cbn [a_base a_off] in Hrd.
  fold (CL5A.uv E' (EVar v)) in Hrd. rewrite Hz, (Z.add_comm z TAB) in Hrd.
  destruct (table_read E' M' z Hr (proj1 (Forall_forall _ _) HK _ (CC.has_cell_In _ _ HT))) as (t0 & Hr0 & Ht0). rewrite Hr0, wle1 in Hrd. injection Hrd as Hrd.
  apply (f_equal bv_unsigned) in Hrd. rewrite Ht0 in Hrd. cbn [edenot] in Hrd. rewrite (u64_of_Z t) in Hrd by lia. rewrite Z_to_bv_unsigned in Hrd. unfold bv_wrap in Hrd.
  change (bv_modulus 8) with 256 in Hrd. rewrite Z.mod_small in Hrd by lia. apply Z.eqb_eq. exact Hrd.
Qed.
Lemma adm_tab_sound : forall v cells lo n f E' (M' : mem) z, adm_tab v cells lo n f = true -> know_ok RSEGS E' M' cells -> CC.has_cell cells TABIMG = true ->
  CL5A.uv E' (EVar v) = z -> lo <= z < lo + Z.of_nat n -> 0 <= z <= 255 -> f z = true.
Proof.
  intros v cells lo n f E' M' z H HK HT Hz Hr Hb. pose proof (RLF.forall_b_sound n lo _ z H Hr) as X. cbn beta in X.
  rewrite (RLF.byte_adm_sound RSEGS v E' M' z cells HK) in X by (rewrite <- Hz; unfold CL5A.uv; cbn [edenot]; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite (tab_cells_sound v cells E' M' z HK HT Hz Hb) in X. exact X.
Qed.
(* [comment removed for export] *)
Definition cls (i : nat) (cells : list kentry) (f : Z -> bool) : bool :=
  (CC.has_cell cells (KBlob (SA CUR0 0) WLEN 1) && CC.has_cell cells TABIMG &&
   match named_at cells (curE i) with
   | Some (_, EVar v, lo, hi) => adm_tab v cells lo (Z.to_nat (hi - lo + 1)) f
   | Some (_, ELit z, _, _) => (Z.leb 0 z && Z.ltb z 256 && f z)%bool
   | _ => false
   end)%bool.
Definition acte (k : Z) (a : pact) (b : Z) : bool := pact_eqb (pn_act k b) a.
(* [comment removed for export] *)
Definition excl_of (i : nat) : option Z := match i with 23%nat => Some 46 | 27%nat => Some 45 | _ => None end.
Definition exclb (i : nat) (b : Z) : bool := match excl_of i with Some x => Z.eqb b x | None => false end.
Definition has_excl (i : nat) : bool := match excl_of i with Some _ => true | None => false end.
Lemma exclb_has : forall i b, has_excl i = false -> exclb i b = false.
Proof. intros i b H. unfold exclb, has_excl in *. destruct (excl_of i); [discriminate H | reflexivity]. Qed.
(* [comment removed for export] *)
Definition jpos (i : nat) (cells : list kentry) : bool := lo_ge cells (jrem i) 1.
Definition jzero (i : nat) (cells : list kentry) : bool := rng_is cells (jrem i) 0.

Definition goto_chkw (i : nat) (cells : list kentry) (j : nat) (s : CC.subst) : bool :=
  let dist := APC.esub (jrem i) (jtgt s j) in
  let d0 := rng_is cells dist 0 in
  let d1 := (rng_is cells dist 1 && jpos i cells)%bool in
  match WK i with
  | WSm => (wkind_eqb (WK j) WGo && rng_is cells (APC.esub WLEN (jtgt s j)) 0 && negb (has_excl j) &&
            match CX.range3 cells NST0 with Some (cn, cn') => Z.eqb cn cn' && Z.eqb cn (NST j) | None => false end)%bool
  | WGo => match WK j with
           | WGo => ((d0 && Z.eqb (NST j) (NST i) && negb (has_excl j)) || (d1 && negb (has_excl j) && cls i cells (fun b => exclb i b || acte (NST i) (PGo (NST j)) b)))%bool
           | WFin => (d0 && Z.eqb (NST j) (NST i) && jpos i cells && cls i cells (fun b => exclb i b || acte (NST i) PEnd b))%bool
           | WErr => (jpos i cells && Z.eqb (NST j) (NST i) && cls i cells (fun b => exclb i b || acte (NST i) (PErr (ERRC j)) b))%bool
           | WRetx => (is_exh i && jzero i cells && match nstc cells with Some (ELit cn) => Z.eqb cn (fixnst (NST i)) | _ => false end)%bool      (* [comment removed for export] *)
           | _ => false
           end
  | WApp | WSetEc | WEnd => wkind_eqb (WK j) WRetx                                                     (* [comment removed for export] *)
  | _ => false
  end.
Definition call_chkw (i : nat) (cells : list kentry) (ps : SR.post_spec) (pc : Z) (j : nat) : bool :=
  if Z.eqb pc PC_SM then (Nat.eqb i 0 && wkind_eqb (WK j) WSm)%bool
  else if Z.eqb pc PC_APPR then
    match WK i, NLIT j with
    | WFin, None => wkind_eqb (WK j) WApp
    | WGo, Some c => (wkind_eqb (WK j) WApp && is_exh i && jzero i cells && Z.eqb c (fixnst (NST i)))%bool
    | _, _ => false
    end
  else if Z.eqb pc PC_ERRH then (wkind_eqb (WK i) WErr && wkind_eqb (WK j) WErrh && Z.eqb (ERRC j) (ERRC i) && negb (Z.eqb (ERRC i) 0))%bool
  else if Z.eqb pc PC_SETEC then
    (wkind_eqb (WK i) WErrh && wkind_eqb (WK j) WSetEc && Z.eqb (ECODE j) (ERRC i) && match reg_of ps 11 with ELit z => Z.eqb (ECODE j) z | _ => false end)%bool
  else if (Z.eqb pc PC_ENDI || Z.eqb pc PC_ENDF)%bool then
    (wkind_eqb (WK i) WApp && wkind_eqb (WK j) WEnd && match NLIT i with None => true | Some _ => false end && CC.has_cell cells (KBlob (SA CUR0 0) WLEN 1)
     && lo_ge cells (APC.esub WEND (curE i)) 1)%bool
  else false.
Definition wl_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto j s => goto_chkw i cells j s
  | CC.TOther pc =>
      if Z.eqb pc RETPC then wkind_eqb (WK i) WRetx
      else if (Z.eqb pc PC_SM || Z.eqb pc PC_ERRH || Z.eqb pc PC_SETEC || Z.eqb pc PC_APPR || Z.eqb pc PC_ENDI || Z.eqb pc PC_ENDF)%bool then
        match ret_of i k with Some (j, _) => call_chkw i cells ps pc j | None => false end
      else match CSLR.find_row ROWS i (SR.ps_pc ps) with                  (* [comment removed for export] *)
           | Some rw => (wkind_eqb (WK i) WGo && (negb (has_excl (CSLR.r_j rw)) || cls i cells (fun b => negb (exclb (CSLR.r_j rw) b))))%bool
           | None => false
           end
  end.
(* [comment removed for export] *)
Definition wl_bad : list (nat * nat) :=
  flat_map (fun i => let c := cutn i in let tags := nth i G.TAGS [] in
                     flat_map (fun k => if wl_chk i c k (nth k (CC.cp_PSS c) (SR.PS 0 [] [] [])) (nth k tags (CC.TOther 0)) then [] else [(i, k)])
                              (seq 0 (length (CC.cp_PSS c)))) (seq 0 NCUT).
Lemma wl_ok : CH2.leaves_all G.CPS G.TAGS wl_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rows_okw : forallb (fun rw => wkind_eqb (WK (CSLR.r_i rw)) WGo && wkind_eqb (WK (CSLR.r_j rw)) WGo && Z.eqb (NST (CSLR.r_j rw)) (NST (CSLR.r_i rw))) ROWS = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma wl_setec : forall i c k ps j, wl_chk i c k ps (CC.TOther PC_SETEC) = true -> CH2.ret_of G.RETS i k = Some j ->
  WK i = WErrh /\ WK j = WSetEc /\ ECODE j = ERRC i /\ reg_of ps 11 = ELit (ECODE j).
Proof.
  intros i c k ps j H Hr. unfold wl_chk in H. cbn [Z.eqb Pos.eqb orb RETPC PC_SM PC_ERRH PC_SETEC PC_APPR PC_ENDI PC_ENDF] in H. unfold ret_of in H. rewrite Hr in H.
  destruct (nth_error G.CPS j) as [cj|]; [|discriminate H]. unfold call_chkw in H. cbn [Z.eqb Pos.eqb orb PC_SM PC_ERRH PC_SETEC PC_APPR] in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply wkind_eqb_eq in H1. apply wkind_eqb_eq in H2. apply Z.eqb_eq in H3. destruct (reg_of ps 11) as [z| | | | | | |]; try discriminate H4. apply Z.eqb_eq in H4. rewrite <- H4.
  exact (conj H1 (conj H2 (conj H3 eq_refl))).
Qed.
Lemma wl_appr : forall i c k ps j, wl_chk i c k ps (CC.TOther PC_APPR) = true -> CH2.ret_of G.RETS i k = Some j ->
  WK j = WApp /\ ((WK i = WFin /\ NLIT j = None) \/
                  (exists cn, WK i = WGo /\ NLIT j = Some cn /\ is_exh i = true /\ jzero i (SR.ps_cells ps) = true /\ cn = fixnst (NST i))).
Proof.
  intros i c k ps j H Hr. unfold wl_chk in H. cbn [Z.eqb Pos.eqb orb RETPC PC_SM PC_ERRH PC_SETEC PC_APPR PC_ENDI PC_ENDF] in H. unfold ret_of in H. rewrite Hr in H.
  destruct (nth_error G.CPS j) as [cj|]; [|discriminate H]. unfold call_chkw in H. cbn [Z.eqb Pos.eqb orb PC_SM PC_ERRH PC_SETEC PC_APPR] in H.
  destruct (WK i); try discriminate H; destruct (NLIT j) as [cn|] eqn:HN; try discriminate H.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply wkind_eqb_eq in H1. apply Z.eqb_eq in H4.
    split; [exact H1|]. right. exists cn. split; [reflexivity|]. split; [reflexivity|]. split; [exact H2|]. split; [exact H3 | exact H4].
  - apply wkind_eqb_eq in H. split; [exact H|]. left. split; reflexivity.
Qed.
Lemma wl_end : forall i c k ps pc j, (pc = PC_ENDI \/ pc = PC_ENDF) -> wl_chk i c k ps (CC.TOther pc) = true -> CH2.ret_of G.RETS i k = Some j ->
  WK i = WApp /\ WK j = WEnd /\ NLIT i = None /\ CC.has_cell (SR.ps_cells ps) (KBlob (SA CUR0 0) WLEN 1) = true /\ lo_ge (SR.ps_cells ps) (APC.esub WEND (curE i)) 1 = true.
Proof.
  intros i c k ps pc j Hpc H Hr. unfold wl_chk in H.
  destruct Hpc as [-> | ->]; cbn [Z.eqb Pos.eqb orb RETPC PC_SM PC_ERRH PC_SETEC PC_APPR PC_ENDI PC_ENDF] in H; unfold ret_of in H; rewrite Hr in H;
    (destruct (nth_error G.CPS j) as [cj|]; [|discriminate H]); unfold call_chkw in H; cbn [Z.eqb Pos.eqb orb PC_SM PC_ERRH PC_SETEC PC_APPR PC_ENDI PC_ENDF] in H;
    apply andb_prop in H as [H H5]; apply andb_prop in H as [H H4]; apply andb_prop in H as [H H3]; apply andb_prop in H as [H1 H2];
    apply wkind_eqb_eq in H1; apply wkind_eqb_eq in H2; (destruct (NLIT i); [discriminate H3|]); exact (conj H1 (conj H2 (conj eq_refl (conj H4 H5)))).
Qed.
(* [comment removed for export] *)
Lemma WK_decl : forall j, kind_of j = KDecl -> WK j = WGo \/ WK j = WFin \/ WK j = WErr.
Proof. intros j H. unfold WK. rewrite H. destruct (Nat.leb j 29); [auto|]. destruct (Nat.leb j 33); [auto|]. destruct (Nat.leb j 38); auto. Qed.
Lemma WK_retx : forall j, WK j = WRetx -> kind_of j = KRetx.
Proof. intros j H. unfold WK in H. destruct (kind_of j); try discriminate H; try reflexivity. destruct (Nat.leb j 29); [discriminate H|]. destruct (Nat.leb j 33); [discriminate H|]. destruct (Nat.leb j 38); discriminate H. Qed.
Lemma wl_errh : forall i c k ps j, wl_chk i c k ps (CC.TOther PC_ERRH) = true -> CH2.ret_of G.RETS i k = Some j ->
  WK i = WErr /\ WK j = WErrh /\ ERRC j = ERRC i /\ ERRC i <> 0.
Proof.
  intros i c k ps j H Hr. unfold wl_chk in H. cbn [Z.eqb Pos.eqb orb RETPC PC_SM PC_ERRH PC_SETEC PC_APPR PC_ENDI PC_ENDF] in H. unfold ret_of in H. rewrite Hr in H.
  destruct (nth_error G.CPS j) as [cj|]; [|discriminate H]. unfold call_chkw in H. cbn [Z.eqb Pos.eqb orb PC_SM PC_ERRH] in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply wkind_eqb_eq in H1. apply wkind_eqb_eq in H2. apply Z.eqb_eq in H3. apply negb_true_iff in H4. apply Z.eqb_neq in H4. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.
End PNCXAW.
