(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_NtStmt LbB_NtK LbB_NtRK LbB_NtD.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_HEmpD LbB_HEmpI LbB_HEmpS LbB_HEmpR LbB_DRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem LbB_RwStm LbB_NtRLR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition R_LOOP : Z := 0xf5ad4.
Definition R_EXIT : Z := 0xf5af0.

Definition keptL : list reg := [1; 2; 3; 4; 5; 8; 9; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv.

Lemma sc_storeok_wr : forall E M (sa : saddr) (A N a : Z) (k : nat),
  wr_at asegs M A N -> adenot E sa = Z_to_bv 64 a -> A <= a -> a + Z.of_nat k <= A + N -> 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  sc_denot asegs M E (SCStoreOk sa k).
Proof.
  intros E M sa A N a k WR Ha HA Hk Ha0 Hk64. cbn [sc_denot]. rewrite Ha.
  replace a with (A + (a - A)) by lia.
  exact (wr_at_store_ok asegs M A N (a - A) k WR ltac:(lia) ltac:(lia)).
Qed.

Lemma agree_of_munch : forall W m m' a k, munch W m m' -> (forall x, a <= x < a + k -> outside W x) ->
  0 <= a -> a + k <= 2 ^ 64 -> agree_on m m' a k.
Proof. intros W m m' a k MU HO Ha Hak i Hi. apply MU. rewrite HLib.u64_of_Z by lia. apply HO. lia. Qed.

Lemma outside_map_inv : forall (l : list (Z * (Z * (Z * Z * Z)))) x e,
  outside (map (fun e => (HRehashModel.addr (Z * Z * Z) e, HRehashModel.addr (Z * Z * Z) e + 8)) l) x -> In e l ->
  ~ (HRehashModel.addr (Z * Z * Z) e <= x < HRehashModel.addr (Z * Z * Z) e + 8).
Proof.
  intros l x e. induction l as [|a l IH]; cbn [map outside In]; intros Ho Hin; [contradiction|].
  destruct Ho as [Ha Ho]. destruct Hin as [<- | Hin]; [exact Ha | exact (IH Ho Hin)].
Qed.

Ltac nrmR HX := rewrite ?w_remu by lia; rewrite ?HX; rewrite ?w_mul by lia; rewrite ?w_add by lia; rewrite ?v_addi_Z by lia.
Ltac sc_brR HX := cbn [sc_denot]; evs; cbn [edenot]; nrmR HX; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia.
Ltac sc_djR HX := cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [edenot a_off a_base]; nrmR HX;
  rewrite ?u64_of_Z by lia; cbn [a_off a_base]; lia.
Ltac sc_shdjR HX :=
  cbn [sc_denot]; unfold flat, elenZ;
  repeat (erewrite estart_sh; [| evs; cbn [edenot]; nrmR HX; reflexivity | lia]);
  unfold estart; cbn [a_base a_off]; evs; cbn [edenot]; nrmR HX; rewrite ?u64_of_Z by lia; cbn [edenot];
  repeat match goal with
  | |- context [?a / 8] =>
      let t := fresh "t" in let Ht := fresh "Ht" in
      pose proof (div8_bound a ltac:(lia)) as Ht; set (t := a / 8) in *; clearbody t
  end;
  rewrite ?u64_of_Z by lia;
  unfold SHBASE; lia.
Ltac sc_flatR HX b := eapply (sc_flat _ _ _ _ b); [evs; cbn [edenot]; nrmR HX; first [reflexivity | f_equal; lia] | lia | cbn; lia | lia | cbn; lia].
Ltac sc_rdR HX C := eapply (sc_read_cellw _ _ _ _ _ _ _ _ C); [cbn; lia | evs; cbn [edenot]; nrmR HX; first [reflexivity | f_equal; lia] | evs; first [reflexivity | f_equal; lia]].
Ltac kshadow_tacR HX :=
  lazymatch goal with
  | |- kentry_ok _ ?E ?M (KWord (SA (EAlu ALU_SRL ?e (ELit 3)) _) 1 (ELit 0)) =>
      eapply kshadow0; [evs; cbn [edenot]; nrmR HX; reflexivity | lia | sh0_from_gz]
  end.
Ltac know_tacR HX := repeat (apply Forall_cons; [first [kshadow_tacR HX | kentry_tac] |]); apply Forall_nil.

Ltac rwc_newR HX Hlf WR :=
  lazymatch goal with |- rw_cells _ (mem_denot ?E ?m ?lg) ?A [?c] =>
    let rec go pre post :=
      lazymatch post with
      | SE ?a ?w ?v :: ?post' =>
          first [ eapply (rw_cells_mem_denot_w E m pre a w v post' A c);
                  [ exact Hlf
                  | repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [edenot a_off a_base]; nrmR HX; rewrite ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; lia|]); apply Forall_nil
                  | unfold estart; evs; cbn [edenot a_off a_base]; nrmR HX; rewrite ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; lia
                  | exact WR | reflexivity | exact I | evs; cbn [edenot cbytes]; rewrite ?w_add, ?w_addm, ?v_addi_Z by lia; reflexivity ]
                | let pre' := eval cbn [app] in (pre ++ [SE a w v]) in go pre' post' ]
      end in
    go (@nil sentry) lg
  end.
Ltac sc_soR HX WR := eapply (sc_storeok_wr _ _ _ _ _ _ _ WR); [evs; cbn [edenot]; nrmR HX; first [reflexivity | f_equal; lia] | lia | cbn; lia | lia | cbn; lia].

Lemma kshadow0_reg : forall E M e (x : Z),
  edenot E e = Z_to_bv 64 (x / 8 + SHBASE) -> 0 <= x < 2 ^ 47 -> sh0 M x ->
  kentry_ok ASEGS E M (KWord (SA e 0) 1 (ELit 0)).
Proof.
  intros E M e x He Hx Hs. cbn [kentry_ok].
  assert (Hd : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hu : bv_unsigned (edenot E e) = x / 8 + SHBASE).
  { rewrite He, Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. unfold SHBASE. lia. }
  split; [lia|]. split.
  - unfold flat, estart. cbn [a_base a_off]. rewrite Hu. unfold SHBASE. lia.
  - unfold adenot. cbn [a_base a_off]. replace (edenot E (ELit 0)) with (Z_to_bv 64 0) by reflexivity.
    rewrite word_to_le_bytes_1 by lia. unfold PropExec.v_addi. rewrite Hu, Z.add_0_r. exact Hs.
Qed.

Definition R_MS : Z := 0xf56a4.

Definition keptX : list reg := [1; 2; 3; 4; 8; 9; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 30; 31]%bv.

Section NtRL.
  Context {HCEIL : HeapCeil}.
  Variables (S1 : Z) (F : bvmap 5 word) (fc : bv 32).
  Variables (obj bl bc p : Z) (ents : list (Z * (Z * (Z * Z * Z)))) (A0 : list (Z * Z)) (M0 ML : mem).
  #[local] Notation n := (bseq_next bc).
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  #[local] Notation addr := (HRehashModel.addr (Z * Z * Z)).
  #[local] Notation hkey := (HRehashModel.hkey (Z * Z * Z)).
  #[local] Notation hh := (HRehashModel.hh (Z * Z * Z) n).
  #[local] Notation sent := (obj + 16).
  #[local] Notation d0 := (LbB_NtRK.d0).
  #[local] Notation st R pc M := (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 pc) M (seg_rom asegs)).

  Hypothesis U0 : umapx MI_A 32 (nval32 ASEGS) A0 M0 obj bl bc ents.
  Hypothesis Hlast : bc <> BSEQ_LAST.
  Hypothesis HP : 0 < p /\ p mod 16 = 0 /\ AIMG_TOP <= p /\ p + 8 * n <= aceil /\ aapp p (8 * n).
  Hypothesis HPN : forall e, In e ents -> apart p (8 * n) (addr e) 32.
  Hypothesis HPO : apart p (8 * n) obj 40.
  Hypothesis OCE : obj + 40 <= aceil.
  Hypothesis OAPP : aapp obj 40.
  Hypothesis NAPP : forall e, In e ents -> aapp (addr e) 32.
  Hypothesis SPR : 2 ^ 45 <= S1 /\ S1 + 672 <= 2 ^ 47.
  Hypothesis ACS : aceil <= S1.
  Hypothesis S616L : rw_cells asegs ML (S1 + 616) [C8 (Z_to_bv 64 SHBASE)].
  Hypothesis S648L : rw_cells asegs ML (S1 + 648) [C8 (Z_to_bv 64 (obj - 136))].

  Definition WL : list (Z * Z) := (p, p + 8 * n) :: (obj + 16, obj + 24) :: map (fun e : ent => (addr e, addr e + 8)) ents.

  Record MSTA (P S : list ent) (Bf : Z -> Z) (M : mem) : Prop := MST {
    m_perm : Permutation (P ++ S) ents;
    m_binv : binv (Z * Z * Z) n sent P Bf;
    m_P : P <> [];
    m_p1 : cell8 ASEGS M sent (hdaddr (P ++ S));
    m_chain : chain ASEGS M (P ++ S);
    m_hash : forall e, In e ents -> cell8 ASEGS M (addr e + 8) (hkey e);
    m_bkt : forall i, 0 <= i < n -> cell8 ASEGS M (p + 8 * i) (Bf i);
    m_adp : addressable M p (8 * n);
    m_adh : addressable M obj 40;
    m_adn : forall e, In e ents -> addressable M (addr e) 32;
    m_mu : munch WL ML M;
    m_wm : wmono asegs ML M;
    m_mi : mem_inv asegs M;
    m_wrp : wr_at asegs M p (8 * n);
    m_wrh : wr_at asegs M obj 40;
    m_wrn : forall e, In e ents -> wr_at asegs M (addr e) 32;
    m_s616 : rw_cells asegs M (S1 + 616) [C8 (Z_to_bv 64 SHBASE)]
  }.

  Record LSTA (P S : list ent) (Bf : Z -> Z) (M : mem) (R : bvmap 5 word) : Prop := LST {
    l_m : MSTA P S Bf M;
    l_x5 : getr R 5%bv = Z_to_bv 64 1;
    l_x9 : getr R 9%bv = Z_to_bv 64 S1;
    l_x10 : getr R 10%bv = Z_to_bv 64 (addr (last P d0));
    l_x14 : getr R 14%bv = Z_to_bv 64 p;
    l_x15 : 2 <= bv_unsigned (getr R 15%bv) <= 64;
    l_x17 : getr R 17%bv = Z_to_bv 64 (hh (last P d0));
    l_x27 : getr R 27%bv = Z_to_bv 64 n;
    l_x29 : getr R 29%bv = Z_to_bv 64 SHBASE;
    l_x31 : getr R 31%bv = Z_to_bv 64 (2 ^ 60)
  }.

  Lemma n_factsL : In n BSEQ /\ bc < n /\ 8 * n <= 2 ^ 28 /\ 0 <= bc.
  Proof.
    destruct (LbB_HEmpR.bseq_next_factsE bc (u_bseq U0) Hlast) as (HnB & Hbcn & Hn28 & _).
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U0)) as Hbc. repeat split; first [exact HnB | lia].
  Qed.

  Lemma chain_last_nil : forall M (P : list ent), chain ASEGS M P -> P <> [] -> cell8 ASEGS M (addr (last P d0)) 0.
  Proof.
    intros M P CH HPn. apply lnk_chain in CH. rewrite (app_removelast_last d0 HPn) in CH.
    apply lnk_app in CH. destruct CH as [_ CH]. cbn [lnk hda] in CH. exact (proj1 CH).
  Qed.

  Lemma last_ent : forall P S, Permutation (P ++ S) ents -> P <> [] -> In (last P d0) ents.
  Proof.
    intros P S HPm HPn. apply (Permutation_in _ HPm). apply in_or_app. left. apply last_in. exact HPn.
  Qed.

  Lemma fld_of_cell8 : forall M a v, cell8 ASEGS M a v -> fldA M a 8 v.
  Proof. intros M a v C. exact (proj2 C). Qed.

  Lemma fld_of_slot : forall M a v, rw_cells asegs M a [C8 (Z_to_bv 64 v)] -> 0 <= v < 2 ^ 64 -> 0 <= a -> fldA M a 8 v.
  Proof. intros M a v RC Hv Ha. exact (proj2 (cellw8_of_rw_cells M a v RC Hv Ha)). Qed.

  Lemma loop_exit : forall P Bf M R, LSTA P [] Bf M R ->
    exists R', CatSim.msteps asegs (st R R_LOOP M) (st R' R_EXIT M) /\ (forall r, In r keptL -> getr R' r = getr R r).
  Proof.
    intros P Bf M R LS. destruct LS as [MS X5 X9 X10 X14 X15 X17 X27 X29 X31].
    pose proof (last_ent P [] (m_perm _ _ _ _ MS) (m_P _ _ _ _ MS)) as Hl.
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hl) as (Hl0 & Hl1 & Hl2 & _).
    pose proof SPR as SPR'.
    assert (F0 : fldA M (addr (last P d0)) 8 0).
    { apply fld_of_cell8. apply chain_last_nil; [| exact (m_P _ _ _ _ MS)].
      pose proof (m_chain _ _ _ _ MS) as CH. rewrite app_nil_r in CH. exact CH. }
    assert (F616 : fldA M (S1 + 616) 8 SHBASE) by (apply fld_of_slot; [exact (m_s616 _ _ _ _ MS) | unfold SHBASE; lia | lia]).
    assert (SH : sh0 M (addr (last P d0))) by (eapply sh0_of_addressable; [exact (m_adn _ _ _ _ MS _ Hl) | change (32 / 8) with 4; lia]).
    set (fx := PropExec.mkFP F fc).
    assert (HR : regs_ok (a0x_E R S1 (addr (last P d0))) a0x_sr R) by (unfold a0x_E, a0x_sr; rw_seedB).
    assert (HK : know_ok bsegs (a0x_E R S1 (addr (last P d0))) M a0x_X_knF) by (unfold a0x_E; knowB).
    assert (HS : scs_denot bsegs M (a0x_E R S1 (addr (last P d0))) a0x_X_scs) by (unfold a0x_X_scs; split_scs).
    destruct (a0x_X_run fx R M (seg_rom asegs) S1 (addr (last P d0)) HS HR HK) as (R' & HR' & HL & Hms).
    change bsegs with asegs in Hms. unfold a0x_X_ss in HR', HL, Hms. cbn [s_regs s_log s_pc mem_denot] in HR', HL, Hms.
    exists R'. split; [exact Hms | keptB HR HR' keptL].
  Qed.

  Definition R_HEAD : Z := 0xf5978.
  Definition R_DISP : Z := 0xf59b4.
  Definition keptA : list reg := [1; 2; 3; 4; 5; 8; 9; 10; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv.
  Definition keptH : list reg := [1; 2; 3; 4; 5; 8; 9; 10; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv.

  Ltac inR := repeat (first [left; reflexivity | right]).
  Ltac hide_mods := repeat match goal with H : ?a mod ?b = 0 |- _ => change (rw_keep (a mod b = 0)) in H end.
  Ltac scs_split := unfold scs_denot; repeat (apply Forall_cons; [|]); try apply Forall_nil.
  Ltac sc_soN HX WR := eapply (sc_storeok_wr _ _ _ _ _ _ _ WR);
    [evs; cbn [edenot]; nrmR HX; first [reflexivity | f_equal; lia] | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia
    | cbn [Z.of_nat Pos.of_succ_nat]; lia].

  Lemma kept_sub : forall r, In r keptL -> In r keptA /\ In r keptH.
  Proof.
    intros r Hr. unfold keptL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [split; [unfold keptA | unfold keptH]; cbn [In]; inR |]). destruct Hr.
  Qed.

  Lemma keptX_sub : forall r, In r keptX -> In r keptL.
  Proof.
    intros r Hr. unfold keptX in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [unfold keptL; cbn [In]; inR |]). destruct Hr.
  Qed.

  Lemma n_pos : 0 < n.
  Proof. pose proof n_factsL as (_ & Hbcn & _ & Hbc). lia. Qed.

  Lemma hh_lt : forall e, 0 <= hh e < n.
  Proof. intros e. exact (HRehashModel.hh_range (Z * Z * Z) n n_pos e). Qed.

  Lemma n_ge5 : ents <> [] -> 5 <= n.
  Proof.
    intros Hne. assert (Hbc : bc <> 0) by (intros E; apply Hne; eapply ents_nil_of_bc0; [exact U0 | exact E]).
    pose proof Hlast as HL. unfold BSEQ_LAST in HL.
    pose proof (u_bseq U0) as HB. unfold BSEQ in HB.
    repeat (destruct HB as [HB | HB]; [first [lia | rewrite <- HB; unfold bseq_next; cbn; lia] |]). destruct HB.
  Qed.

  Lemma node_apart_obj : forall e, In e ents -> apart (addr e) 32 obj 40.
  Proof. intros [q [k v]] He. destruct (u_node U0 q k v He) as (_ & _ & _ & _ & _ & _ & _ & _ & Hap & _). exact Hap. Qed.

  Lemma outside_mapI : forall (l : list ent) x, (forall e, In e l -> ~ (addr e <= x < addr e + 8)) ->
    outside (map (fun e : ent => (addr e, addr e + 8)) l) x.
  Proof.
    induction l as [|a l IH]; intros x H; cbn [map outside]; [exact I|].
    split; [apply H; left; reflexivity | apply IH; intros e He; apply H; right; exact He].
  Qed.

  Lemma wl_hash : forall e y, In e ents -> addr e + 8 <= y < addr e + 16 -> outside WL y.
  Proof.
    intros e y He Hy. pose proof (HPN e He) as A1. pose proof (node_apart_obj e He) as A2. unfold apart in A1, A2.
    unfold WL. cbn [outside]. split; [lia|]. split; [lia|]. apply outside_mapI. intros e' He'.
    destruct (Z.eq_dec (addr e') (addr e)) as [Eq | Ne]; [lia|].
    pose proof (nodes_apart _ _ _ _ _ _ _ _ U0 He' He Ne) as A3. unfold apart in A3. lia.
  Qed.

  Lemma wl_shadow : forall y, ALOWSH_LO <= y < AHI_LO -> outside WL y.
  Proof.
    intros y Hy. destruct HP as (_ & _ & _ & _ & HA). pose proof OAPP as HO.
    unfold aapp, aapp_lo, aapp_hi in HA, HO. unfold ALOWSH_LO, AHI_LO in *.
    unfold WL. cbn [outside]. split; [lia|]. split; [lia|]. apply outside_mapI. intros e He.
    pose proof (NAPP e He) as HN. unfold aapp, aapp_lo, aapp_hi in HN. unfold ALOWSH_LO, AHI_LO in HN. lia.
  Qed.

  Lemma wl_high : forall y, aceil <= y -> 2 ^ 45 <= y -> outside WL y.
  Proof.
    intros y Hy Hy'. destruct HP as (_ & _ & _ & HPc & _). pose proof OCE as HO.
    unfold WL. cbn [outside]. split; [lia|]. split; [lia|]. apply outside_mapI. intros e He.
    pose proof (NAPP e He) as HN. unfold aapp, aapp_lo, aapp_hi in HN. unfold ALOWSH_LO in HN. lia.
  Qed.

  Lemma adr_keep : forall M M' A k, munch WL M M' -> addressable M A k -> 0 <= A -> A + k <= 2 ^ 47 -> addressable M' A k.
  Proof.
    intros M M' A k MU AD HA HAk. apply (LbB_DRep.addressable_pteq M M' A k AD). intros y Hy.
    destruct AD as [Hk _]. pose proof (sh_nsh_high A k HA Hk HAk) as Hh.
    assert (H8 : 0 <= A / 8) by (apply Z.div_pos; lia).
    unfold sh in Hy, Hh. rewrite ASHADOW_BASE_val in Hy, Hh. unfold AHI_LO in Hh.
    apply MU. try unfold wa. rewrite u64_of_Z by lia. apply wl_shadow. unfold ALOWSH_LO, AHI_LO. lia.
  Qed.

  Lemma wr_keep : forall M M' a k, wmono asegs M M' -> wr_at asegs M a k -> wr_at asegs M' a k.
  Proof. intros M M' a k WM (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. apply WM. exact (W3 i Hi). Qed.

  Lemma cell8_keep : forall W M M' a v, munch W M M' -> cell8 ASEGS M a v -> (forall y, a <= y < a + 8 -> outside W y) ->
    0 <= a -> a + 8 <= 2 ^ 64 -> cell8 ASEGS M' a v.
  Proof. intros W M M' a v MU C HO Ha Ha8. eapply cellw_agree; [exact C | exact (agree_of_munch W M M' a 8 MU HO Ha Ha8) | lia | cbn; lia]. Qed.

  Lemma msta_keep : forall P S Bf M M' P' S' Bf',
    MSTA P S Bf M -> munch WL M M' -> wmono asegs M M' -> mem_inv asegs M' ->
    Permutation (P' ++ S') ents -> binv (Z * Z * Z) n sent P' Bf' -> P' <> [] ->
    cell8 ASEGS M' sent (hdaddr (P' ++ S')) -> chain ASEGS M' (P' ++ S') ->
    (forall i, 0 <= i < n -> cell8 ASEGS M' (p + 8 * i) (Bf' i)) -> MSTA P' S' Bf' M'.
  Proof.
    intros P S Bf M M' P' S' Bf' MS MU WM MI PM BI PN C1 CH BK.
    pose proof SPR as SPR'. pose proof HP as (HP0 & HP1 & HP2 & HP3 & _). pose proof n_factsL as NF. pose proof (u_obj_lo U0) as O1. pose proof (u_obj_hi U0) as O2.
    constructor; try assumption.
    - intros e He. destruct (ent_facts _ _ _ _ _ _ _ U0 He) as (He0 & He1 & _ & _).
      apply (cell8_keep WL M); [exact MU | exact (m_hash _ _ _ _ MS e He) | intros y Hy; apply (wl_hash e y He); lia | lia | lia].
    - apply (adr_keep M); [exact MU | exact (m_adp _ _ _ _ MS) | lia | lia].
    - apply (adr_keep M); [exact MU | exact (m_adh _ _ _ _ MS) | lia | lia].
    - intros e He. destruct (ent_facts _ _ _ _ _ _ _ U0 He) as (He0 & He1 & _ & _).
      apply (adr_keep M); [exact MU | exact (m_adn _ _ _ _ MS e He) | lia | lia].
    - intros y Hy. rewrite (MU y Hy). exact (m_mu _ _ _ _ MS y Hy).
    - intros y Hy. apply WM. exact (m_wm _ _ _ _ MS y Hy).
    - apply (wr_keep M); [exact WM | exact (m_wrp _ _ _ _ MS)].
    - apply (wr_keep M); [exact WM | exact (m_wrh _ _ _ _ MS)].
    - intros e He. apply (wr_keep M); [exact WM | exact (m_wrn _ _ _ _ MS e He)].
    - apply rw_cells_of_cellw8; [| unfold AIMG_TOP; lia | lia].
      apply (cell8_keep WL M); [exact MU | | intros y Hy; apply wl_high; lia | lia | lia].
      apply cellw8_of_rw_cells; [exact (m_s616 _ _ _ _ MS) | unfold SHBASE; lia | lia].
  Qed.

  Record HSTA (P : list ent) (x : ent) (S : list ent) (Bf : Z -> Z) (M : mem) (R : bvmap 5 word) : Prop := HST {
    h_m : MSTA P (x :: S) Bf M;
    h_x5 : getr R 5%bv = Z_to_bv 64 1;
    h_x9 : getr R 9%bv = Z_to_bv 64 S1;
    h_x10 : getr R 10%bv = Z_to_bv 64 (addr (last P d0));
    h_x11 : getr R 11%bv = Z_to_bv 64 (addr x);
    h_x14 : getr R 14%bv = Z_to_bv 64 p;
    h_x15 : 2 <= bv_unsigned (getr R 15%bv) <= 64;
    h_x17 : getr R 17%bv = Z_to_bv 64 (hh (last P d0));
    h_x27 : getr R 27%bv = Z_to_bv 64 n;
    h_x29 : getr R 29%bv = Z_to_bv 64 SHBASE;
    h_x31 : getr R 31%bv = Z_to_bv 64 (2 ^ 60)
  }.

  Lemma loop_enter : forall P x S' Bf M R, LSTA P (x :: S') Bf M R ->
    exists R', CatSim.msteps asegs (st R R_LOOP M) (st R' R_HEAD M) /\ HSTA P x S' Bf M R'
               /\ (forall r, In r keptA -> getr R' r = getr R r).
  Proof.
    intros P x S' Bf M R LS. destruct LS as [MS X5 X9 X10 X14 X15 X17 X27 X29 X31].
    pose proof (last_ent P (x :: S') (m_perm _ _ _ _ MS) (m_P _ _ _ _ MS)) as Hl.
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hl) as (Hl0 & Hl1 & Hl2 & _).
    assert (Hx : In x ents) by (apply (Permutation_in _ (m_perm _ _ _ _ MS)); apply in_or_app; right; left; reflexivity).
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hx) as (Hx0 & Hx1 & Hx2 & _).
    pose proof SPR as SPR'.
    assert (F0 : fldA M (addr (last P d0)) 8 (addr x)).
    { apply fld_of_cell8. exact (chain_last_next M P x S' (m_chain _ _ _ _ MS) (m_P _ _ _ _ MS)). }
    assert (F616 : fldA M (S1 + 616) 8 SHBASE) by (apply fld_of_slot; [exact (m_s616 _ _ _ _ MS) | unfold SHBASE; lia | lia]).
    assert (SH : sh0 M (addr (last P d0))) by (eapply sh0_of_addressable; [exact (m_adn _ _ _ _ MS _ Hl) | change (32 / 8) with 4; lia]).
    set (fx := PropExec.mkFP F fc).
    assert (HR : regs_ok (a0c_E R S1 (addr (last P d0)) (addr x)) a0c_sr R) by (unfold a0c_E, a0c_sr; rw_seedB).
    assert (HK : know_ok bsegs (a0c_E R S1 (addr (last P d0)) (addr x)) M a0c_C_knF) by (unfold a0c_E; knowB).
    assert (HS : scs_denot bsegs M (a0c_E R S1 (addr (last P d0)) (addr x)) a0c_C_scs) by (unfold a0c_C_scs; split_scs).
    destruct (a0c_C_run fx R M (seg_rom asegs) S1 (addr (last P d0)) (addr x) HS HR HK) as (R' & HR' & HL & Hms).
    change bsegs with asegs in Hms. unfold a0c_C_ss in HR', HL, Hms. cbn [s_regs s_log s_pc mem_denot] in HR', HL, Hms.
    assert (KP : forall r, In r keptA -> getr R' r = getr R r) by (keptB HR HR' keptA).
    rreg_ HR' (11%bv : bv 5) H11.
    exists R'. split; [exact Hms|]. split; [|exact KP].
    constructor; [exact MS | | | | exact H11 | | | | | |];
      rewrite ?KP by (unfold keptA; cbn [In]; inR); assumption.
  Qed.

  Record DSTA (P : list ent) (x : ent) (S : list ent) (Bf : Z -> Z) (M : mem) (R : bvmap 5 word) : Prop := DST {
    d_h : HSTA P x S Bf M R;
    d_x13 : getr R 13%bv = Z_to_bv 64 (hh x)
  }.

  Lemma head_hash : forall P x S' Bf M R, HSTA P x S' Bf M R ->
    exists R', CatSim.msteps asegs (st R R_HEAD M) (st R' R_DISP M) /\ DSTA P x S' Bf M R'
               /\ (forall r, In r keptH -> getr R' r = getr R r).
  Proof.
    intros P x S' Bf M R HS0. destruct HS0 as [MS X5 X9 X10 X11 X14 X15 X17 X27 X29 X31].
    assert (Hx : In x ents) by (apply (Permutation_in _ (m_perm _ _ _ _ MS)); apply in_or_app; right; left; reflexivity).
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hx) as (Hx0 & Hx1 & Hx2 & Hk).
    assert (Hne : ents <> []) by (intros E; rewrite E in Hx; destruct Hx).
    pose proof (n_ge5 Hne) as N5. pose proof n_factsL as (_ & _ & N28 & _).
    pose proof SPR as SPR'.
    pose proof X15 as X15o.
    assert (X15' : getr R 15%bv = Z_to_bv 64 (bv_unsigned (getr R 15%bv))) by (symmetry; apply Z_to_bv_bv_unsigned).
    revert X15 X15'. generalize (bv_unsigned (getr R 15%bv)) as pc. intros pc X15 X15'.
    assert (F616 : fldA M (S1 + 616) 8 SHBASE) by (apply fld_of_slot; [exact (m_s616 _ _ _ _ MS) | unfold SHBASE; lia | lia]).
    assert (F8 : fldA M (addr x + 8) 8 (hkey x)) by (apply fld_of_cell8; exact (m_hash _ _ _ _ MS x Hx)).
    assert (SH : sh0 M (addr x + 8)) by (eapply sh0_of_addressable; [exact (m_adn _ _ _ _ MS _ Hx) | change (32 / 8) with 4; lia]).
    set (fx := PropExec.mkFP F fc).
    assert (HR : regs_ok (a1_E R S1 pc n (addr x) (hkey x)) a1_sr R) by (unfold a1_E, a1_sr; rw_seedB).
    destruct (Z_lt_ge_dec (hkey x) n) as [Hlt | Hge].
    - assert (HK : know_ok bsegs (a1_E R S1 pc n (addr x) (hkey x)) M a1_L_knF) by (unfold a1_E; knowB).
      assert (HX : Z.succ 0 = 1) by reflexivity.
      assert (HS : scs_denot bsegs M (a1_E R S1 pc n (addr x) (hkey x)) a1_L_scs) by (unfold a1_L_scs, a1_E; split_scs; sc_brR HX).
      destruct (a1_L_run fx R M (seg_rom asegs) S1 pc n (addr x) (hkey x) HS HR HK) as (R' & HR' & HL & Hms).
      change bsegs with asegs in Hms. unfold a1_L_ss in HR', HL, Hms. cbn [s_regs s_log s_pc mem_denot] in HR', HL, Hms.
      assert (KP : forall r, In r keptH -> getr R' r = getr R r) by (keptB HR HR' keptH).
      rreg_ HR' (13%bv : bv 5) H13.
      exists R'. split; [exact Hms|]. split; [|exact KP].
      constructor; [constructor; [exact MS | | | | | | | | | |] |];
        rewrite ?KP by (unfold keptH; cbn [In]; inR); try assumption.
      rewrite H13. f_equal. unfold HRehashModel.hh, hmod. rewrite Z.mod_small by lia. reflexivity.
    - assert (HK : know_ok bsegs (a1_E R S1 pc n (addr x) (hkey x)) M a1_G_knF) by (unfold a1_E; knowB).
      assert (HX : Z.succ 0 = 1) by reflexivity.
      assert (HS : scs_denot bsegs M (a1_E R S1 pc n (addr x) (hkey x)) a1_G_scs) by (unfold a1_G_scs, a1_E; split_scs; sc_brR HX).
      destruct (a1_G_run fx R M (seg_rom asegs) S1 pc n (addr x) (hkey x) HS HR HK) as (R' & HR' & HL & Hms).
      change bsegs with asegs in Hms. unfold a1_G_ss in HR', HL, Hms. cbn [s_regs s_log s_pc mem_denot] in HR', HL, Hms.
      assert (KP : forall r, In r keptH -> getr R' r = getr R r) by (keptB HR HR' keptH).
      rreg_ HR' (13%bv : bv 5) H13.
      exists R'. split; [exact Hms|]. split; [|exact KP].
      constructor; [constructor; [exact MS | | | | | | | | | |] |];
        rewrite ?KP by (unfold keptH; cbn [In]; inR); try assumption.
      rewrite H13. unfold a1_E. evs. rewrite w_remu by lia. reflexivity.
  Qed.
  Lemma disp_same : forall P x S' Bf M R, DSTA P x S' Bf M R -> hh x = hh (last P d0) ->
    exists R', CatSim.msteps asegs (st R R_DISP M) (st R' R_LOOP M) /\ LSTA (P ++ [x]) S' Bf M R'
               /\ (forall r, In r keptL -> getr R' r = getr R r).
  Proof.
    intros P x S' Bf M R DS Hh. destruct DS as [[MS X5 X9 X10 X11 X14 X15 X17 X27 X29 X31] X13].
    pose proof (m_P _ _ _ _ MS) as HPn.
    pose proof (last_ent P (x :: S') (m_perm _ _ _ _ MS) HPn) as Hl.
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hl) as (Hl0 & Hl1 & Hl2 & _).
    assert (Hx : In x ents) by (apply (Permutation_in _ (m_perm _ _ _ _ MS)); apply in_or_app; right; left; reflexivity).
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hx) as (Hx0 & Hx1 & Hx2 & _).
    assert (Hne : ents <> []) by (intros E; rewrite E in Hx; destruct Hx).
    pose proof (n_ge5 Hne) as N5. pose proof n_factsL as (_ & _ & N28 & _).
    pose proof (hh_lt x) as Hhx. pose proof (hh_lt (last P d0)) as Hhl.
    pose proof SPR as SPR'. pose proof HP as (HP0 & HP1 & HP2 & HP3 & _). unfold AIMG_TOP in HP2.
    assert (Hl8 : addr (last P d0) mod 8 = 0) by (clear - Hl2; Z.div_mod_to_equations; lia).
    assert (F616 : fldA M (S1 + 616) 8 SHBASE) by (apply fld_of_slot; [exact (m_s616 _ _ _ _ MS) | unfold SHBASE; lia | lia]).
    set (fx := PropExec.mkFP F fc).
    assert (HR : regs_ok (bs_E R S1 (addr (last P d0)) p n (hh (last P d0)) (addr x) (hh x) 0 0 0) bs_sr R)
      by (unfold bs_E, bs_sr; rw_seedB).
    assert (HK : know_ok bsegs (bs_E R S1 (addr (last P d0)) p n (hh (last P d0)) (addr x) (hh x) 0 0 0) M bs_S_knF)
      by (unfold bs_E; knowB).
    assert (HX : Z.succ 0 = 1) by reflexivity.
    assert (HS : scs_denot bsegs M (bs_E R S1 (addr (last P d0)) p n (hh (last P d0)) (addr x) (hh x) 0 0 0) bs_S_scs)
      by (unfold bs_S_scs, bs_E; split_scs; sc_brR HX).
    destruct (bs_S_run fx R M (seg_rom asegs) S1 (addr (last P d0)) p n (hh (last P d0)) (addr x) (hh x) 0 0 0 HS HR HK)
      as (R' & HR' & HL & Hms).
    change bsegs with asegs in Hms. unfold bs_S_ss in HR', HL, Hms. cbn [s_regs s_log s_pc mem_denot] in HR', HL, Hms.
    assert (KP : forall r, In r keptL -> getr R' r = getr R r) by (keptB HR HR' keptL).
    rreg_ HR' (10%bv : bv 5) H10. rreg_ HR' (17%bv : bv 5) H17.
    exists R'. split; [exact Hms|]. split; [|exact KP].
    assert (HPx : P ++ [x] <> []) by (intros E; apply app_eq_nil in E; destruct E as [_ E]; discriminate).
    constructor; rewrite ?KP by (unfold keptL; cbn [In]; inR); try assumption.
    - apply (msta_keep P (x :: S') Bf M M); [exact MS | apply munch_refl | intros y Hy; exact Hy | exact (m_mi _ _ _ _ MS)
        | | | exact HPx | | | exact (m_bkt _ _ _ _ MS)]; try (rewrite <- app_assoc; cbn [app]).
      + exact (m_perm _ _ _ _ MS).
      + apply HRehashModel.step_same; [exact (m_binv _ _ _ _ MS) | exact HPn | rewrite Hh; f_equal; apply last_any; exact HPn].
      + exact (m_p1 _ _ _ _ MS).
      + exact (m_chain _ _ _ _ MS).
    - rewrite H10. unfold bs_E. evs. rewrite last_last. reflexivity.
    - rewrite H17. unfold bs_E. evs. rewrite last_last. rewrite Hh. reflexivity.
  Qed.

  Lemma disp_empty : forall P x S' Bf M R, DSTA P x S' Bf M R -> hh x <> hh (last P d0) -> Bf (hh x) = 0 ->
    exists R' M', CatSim.msteps asegs (st R R_DISP M) (st R' R_LOOP M')
      /\ LSTA (P ++ [x]) S' (fun i => if i =? hh x then addr (last P d0) else Bf i) M' R'
      /\ (forall r, In r keptL -> getr R' r = getr R r).
  Proof.
    intros P x S' Bf M R DS Hh Hb0. destruct DS as [[MS X5 X9 X10 X11 X14 X15 X17 X27 X29 X31] X13].
    pose proof (m_P _ _ _ _ MS) as HPn.
    pose proof (last_ent P (x :: S') (m_perm _ _ _ _ MS) HPn) as Hl.
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hl) as (Hl0 & Hl1 & Hl2 & _).
    assert (Hx : In x ents) by (apply (Permutation_in _ (m_perm _ _ _ _ MS)); apply in_or_app; right; left; reflexivity).
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hx) as (Hx0 & Hx1 & Hx2 & _).
    assert (Hne : ents <> []) by (intros E; rewrite E in Hx; destruct Hx).
    pose proof (n_ge5 Hne) as N5. pose proof n_factsL as (_ & _ & N28 & _).
    pose proof (hh_lt x) as Hhx. pose proof (hh_lt (last P d0)) as Hhl.
    pose proof SPR as SPR'. pose proof HP as (HP0 & HP1 & HP2 & HP3 & _). unfold AIMG_TOP in HP2.
    pose proof HPO as HPO'. unfold apart in HPO'. pose proof (u_obj_lo U0) as O1. pose proof (u_obj_hi U0) as O2.
    assert (Hl8 : addr (last P d0) mod 8 = 0) by (clear - Hl2; Z.div_mod_to_equations; lia).
    assert (F616 : fldA M (S1 + 616) 8 SHBASE) by (apply fld_of_slot; [exact (m_s616 _ _ _ _ MS) | unfold SHBASE; lia | lia]).
    assert (SHB : sh0 M (p + 8 * hh x)).
    { eapply sh0_of_addressable; [exact (m_adp _ _ _ _ MS) |]. rewrite (Z.mul_comm 8 n), Z.div_mul by lia. lia. }
    assert (C0 : cell8 ASEGS M (p + 8 * hh x) 0) by (rewrite <- Hb0; exact (m_bkt _ _ _ _ MS (hh x) Hhx)).
    pose proof (m_wrp _ _ _ _ MS) as WRp.
    assert (WRb : wr_at asegs M (p + 8 * hh x) 8) by (eapply LbB_DRep.wr_at_sub; [exact WRp | lia | lia | lia]).
    set (fx := PropExec.mkFP F fc).
    assert (HR : regs_ok (be_E R S1 (addr (last P d0)) p n (hh (last P d0)) (addr x) (hh x) 0 0 0) be_sr R)
      by (unfold be_E, be_sr; rw_seedB).
    assert (HK : know_ok bsegs (be_E R S1 (addr (last P d0)) p n (hh (last P d0)) (addr x) (hh x) 0 0 0) M be_E_knF)
      by (unfold be_E; knowB).
    assert (HX : Z.succ 0 = 1) by reflexivity.
    assert (HS : scs_denot bsegs M (be_E R S1 (addr (last P d0)) p n (hh (last P d0)) (addr x) (hh x) 0 0 0) be_E_scs)
      by (unfold be_E_scs, be_E; scs_split; [sc_soN HX WRp | sc_brR HX | sc_rdR HX C0 | sc_brR HX | sc_brR HX]).
    destruct (be_E_run fx R M (seg_rom asegs) S1 (addr (last P d0)) p n (hh (last P d0)) (addr x) (hh x) 0 0 0 HS HR HK)
      as (R' & HR' & HL & Hms).
    change bsegs with asegs in Hms. unfold be_E_ss in HR', HL, Hms. cbn [s_regs s_log s_pc] in HR', HL, Hms.
    assert (KP : forall r, In r keptL -> getr R' r = getr R r) by (keptB HR HR' keptL).
    rreg_ HR' (10%bv : bv 5) H10. rreg_ HR' (17%bv : bv 5) H17.
    pose proof (munch_log _ M _ HL) as MUL.
    assert (MI' := msteps_mem_inv _ _ _ Hms (m_mi _ _ _ _ MS)). cbn [ms_mem] in MI'.
    lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ (mem_denot ?EE ?m0 ?lg) _) =>
      let MM := constr:(mem_denot EE m0 lg) in
      assert (CB : rw_cells asegs MM (p + 8 * hh x) [C8 (Z_to_bv 64 (addr (last P d0)))]) by (unfold be_E; rwc_newR HX HL WRb);
      assert (MUW : munch WL M MM) by (apply munch_mem_denot; [exact HL | apply Forall_cons; [| apply Forall_nil];
        cbn [e_addr e_width]; unfold WL; cbn [inside]; left; unfold estart, be_E; evs; cbn [edenot a_base a_off]; nrmR HX;
        rewrite ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia]);
      assert (MU1 : munch [(p + 8 * hh x, p + 8 * hh x + 8)] M MM) by (eapply munch_eqW; [exact MUL |];
        unfold log_ivs; cbn [map e_addr e_width]; unfold estart, be_E; evs; cbn [edenot a_base a_off]; nrmR HX;
        rewrite ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat]; f_equal; f_equal; lia);
      pose proof (wmono_mem_denot EE m0 lg) as WM;
      remember MM as M' eqn:HM'
    end.
    clear HM'.
    apply cellw8_of_rw_cells in CB; [| lia | lia].
    exists R', M'. split; [exact Hms|]. split; [|exact KP].
    assert (HPx : P ++ [x] <> []) by (intros E; apply app_eq_nil in E; destruct E as [_ E]; discriminate).
    constructor; rewrite ?KP by (unfold keptL; cbn [In]; inR); try assumption.
    - apply (msta_keep P (x :: S') Bf M M'); [exact MS | exact MUW | exact WM | exact MI' | | | exact HPx | | |];
        try (rewrite <- app_assoc; cbn [app]).
      + exact (m_perm _ _ _ _ MS).
      + pose proof (HRehashModel.step_empty (Z * Z * Z) n sent P x Bf (m_binv _ _ _ _ MS) HPn n_pos) as BI'.
        assert (Hlx : addr (last P x) <> 0) by (rewrite (last_any P x d0 HPn); lia).
        replace (last P d0) with (last P x) by (apply last_any; exact HPn). exact (BI' Hlx).
      + apply (cell8_keep _ M M' _ _ MU1 (m_p1 _ _ _ _ MS)); [| lia | lia].
        intros y Hy. cbn [outside]. split; [lia | exact I].
      + eapply chain_agree; [exact (m_chain _ _ _ _ MS) |]. intros q k v Hq.
        assert (Hqe : In (q, (k, v)) ents) by (exact (Permutation_in _ (m_perm _ _ _ _ MS) Hq)).
        pose proof (HPN _ Hqe) as Aq. unfold apart in Aq. cbn [HRehashModel.addr fst] in Aq.
        destruct (ent_facts _ _ _ _ _ _ _ U0 Hqe) as (Hq0 & Hq1 & _ & _). cbn [HRehashModel.addr fst] in Hq0, Hq1.
        split; [| lia]. apply (agree_of_munch _ M M' q 8 MU1); [| lia | lia].
        intros y Hy. cbn [outside]. split; [lia | exact I].
      + intros i Hi. cbv beta. destruct (Z.eqb_spec i (hh x)) as [-> | Hi'].
        * exact CB.
        * apply (cell8_keep _ M M' _ _ MU1 (m_bkt _ _ _ _ MS i Hi)); [| lia | lia].
          intros y Hy. cbn [outside]. split; [lia | exact I].
    - rewrite H10. unfold be_E. evs. rewrite last_last. reflexivity.
    - rewrite H17. unfold be_E. evs. rewrite last_last. reflexivity.
  Qed.
  Lemma munch_widen : forall W1 M M', munch W1 M M' -> (forall y, outside WL y -> outside W1 y) -> munch WL M M'.
  Proof. intros W1 M M' MU H y Hy. exact (MU y (H _ Hy)). Qed.

  Lemma hd_range : forall S, (forall e, In e S -> In e ents) -> 0 <= hdaddr S < 2 ^ 47.
  Proof.
    intros [|e S] H; cbn [hdaddr]; [lia|]. destruct e as [q kv].
    destruct (ent_facts _ _ _ _ _ _ _ U0 (H _ (or_introl eq_refl))) as (Hq0 & Hq1 & _ & _). cbn in Hq0, Hq1. lia.
  Qed.

  Lemma inside_mapN : forall (l : list ent) e, In e l -> inside (map (fun e : ent => (addr e, addr e + 8)) l) (addr e) 8.
  Proof.
    induction l as [|a l IH]; intros e He; [destruct He|].
    destruct He as [<- | He]; cbn [map inside]; [left; lia | right; exact (IH e He)].
  Qed.

  Ltac sc_brA HX := cbn [sc_denot]; evs; cbn [edenot]; rewrite ?land7_val by lia; nrmR HX;
    rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia.

  Lemma disp_splice : forall P x S' Bf M R, DSTA P x S' Bf M R -> hh x <> hh (last P d0) -> Bf (hh x) <> 0 ->
    exists R' M' P', CatSim.msteps asegs (st R R_DISP M) (st R' R_LOOP M') /\ LSTA P' S' Bf M' R'
      /\ (forall r, In r keptL -> getr R' r = getr R r).
  Proof.
    intros P x S' Bf M R DS Hh Hb0. destruct DS as [[MS X5 X9 X10 X11 X14 X15 X17 X27 X29 X31] X13].
    pose proof (m_P _ _ _ _ MS) as HPn. pose proof (m_perm _ _ _ _ MS) as PM.
    assert (HE : forall e, In e (P ++ x :: S') -> In e ents) by (intros e He; exact (Permutation_in _ PM He)).
    pose proof (last_ent P (x :: S') PM HPn) as Hl.
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hl) as (Hl0 & Hl1 & Hl2 & _).
    assert (Hx : In x ents) by (apply HE; apply in_or_app; right; left; reflexivity).
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hx) as (Hx0 & Hx1 & Hx2 & _).
    assert (Hne : ents <> []) by (intros E; rewrite E in Hx; destruct Hx).
    pose proof (n_ge5 Hne) as N5. pose proof n_factsL as (_ & _ & N28 & _).
    pose proof (hh_lt x) as Hhx. pose proof (hh_lt (last P d0)) as Hhl.
    pose proof SPR as SPR'. pose proof HP as (HP0 & HP1 & HP2 & HP3 & HPa). unfold AIMG_TOP in HP2.
    pose proof HPO as HPO'. unfold apart in HPO'. pose proof (u_obj_lo U0) as O1. pose proof (u_obj_hi U0) as O2.
    pose proof (u_obj_al U0) as O3.
    assert (Hl8 : addr (last P d0) mod 8 = 0) by (clear - Hl2; Z.div_mod_to_equations; lia).
    hide_mods.
    assert (Hxl : addr x <> addr (last P d0)).
    { intros E. pose proof (perm_nodup _ _ _ _ _ _ _ U0 PM) as ND.
      exact (nodup_app_ne P (x :: S') (last P d0) x ND (last_in P d0 HPn) (or_introl eq_refl) (eq_sym E)). }
    pose proof (nodes_apart _ _ _ _ _ _ _ _ U0 Hx Hl Hxl) as Axl. unfold apart in Axl.
    pose proof (HPN x Hx) as Apx. pose proof (HPN _ Hl) as Apl. unfold apart in Apx, Apl.
    pose proof (node_apart_obj x Hx) as Aox. pose proof (node_apart_obj _ Hl) as Aol. unfold apart in Aox, Aol.
    pose proof (NAPP x Hx) as Nx. pose proof (NAPP _ Hl) as Nl. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in Nx, Nl.
    assert (F616 : fldA M (S1 + 616) 8 SHBASE) by (apply fld_of_slot; [exact (m_s616 _ _ _ _ MS) | unfold SHBASE; lia | lia]).
    assert (SHB : sh0 M (p + 8 * hh x)).
    { eapply sh0_of_addressable; [exact (m_adp _ _ _ _ MS) |]. rewrite (Z.mul_comm 8 n), Z.div_mul by lia. lia. }
    assert (SHx : sh0 M (addr x)) by (eapply sh0_of_addressable; [exact (m_adn _ _ _ _ MS _ Hx) | change (32 / 8) with 4; lia]).
    assert (SHl : sh0 M (addr (last P d0))) by (eapply sh0_of_addressable; [exact (m_adn _ _ _ _ MS _ Hl) | change (32 / 8) with 4; lia]).
    assert (Fx : fldA M (addr x) 8 (hdaddr S')) by (apply fld_of_cell8; exact (chain_head_next M P x S' (m_chain _ _ _ _ MS))).
    assert (Hhd : 0 <= hdaddr S' < 2 ^ 47) by (apply hd_range; intros e He; apply HE; apply in_or_app; right; right; exact He).
    pose proof (m_wrp _ _ _ _ MS) as WRp.
    assert (WRx : wr_at asegs M (addr x) 8) by (eapply LbB_DRep.wr_at_sub; [exact (m_wrn _ _ _ _ MS _ Hx) | lia | lia | lia]).
    assert (WRl : wr_at asegs M (addr (last P d0)) 8) by (eapply LbB_DRep.wr_at_sub; [exact (m_wrn _ _ _ _ MS _ Hl) | lia | lia | lia]).
    assert (Cb : cell8 ASEGS M (p + 8 * hh x) (Bf (hh x))) by exact (m_bkt _ _ _ _ MS (hh x) Hhx).
    destruct (splice_facts _ _ _ _ _ _ _ P S' Bf x M U0 PM (m_binv _ _ _ _ MS) HPn (m_p1 _ _ _ _ MS) (m_chain _ _ _ _ MS) Hhx Hb0)
      as (nt & P' & Cnt & Hnt & Hcase & Hlast' & HP'n & PERM' & BI' & POST).
    assert (BVc : Bf (hh x) = sent \/ exists y, In y ents /\ Bf (hh x) = addr y /\ addr y <> addr (last P d0) /\ addr y <> addr x).
    { destruct Hcase as [Hs | (y & Hy & Hyb & Hy1 & Hy2)]; [left; exact Hs | right; exists y].
      split; [apply HE; apply in_or_app; left; exact Hy | auto]. }
    assert (BV : 0 < Bf (hh x) /\ Bf (hh x) + 16 <= 2 ^ 47 /\ Bf (hh x) mod 8 = 0 /\ wr_at asegs M (Bf (hh x)) 8
      /\ sh0 M (Bf (hh x)) /\ (forall e, In e ents -> addr e <> Bf (hh x) -> addr e + 8 <= Bf (hh x) \/ Bf (hh x) + 8 <= addr e)
      /\ (p + 8 * n <= Bf (hh x) \/ Bf (hh x) + 8 <= p) /\ addr (last P d0) <> Bf (hh x) /\ addr x <> Bf (hh x)
      /\ (Bf (hh x) <> sent -> obj + 40 <= Bf (hh x) \/ Bf (hh x) + 8 <= obj)
      /\ (ALOWSH_LO <= Bf (hh x) -> AHI_LO <= Bf (hh x))).
    { destruct BVc as [Hs | (y & Hy & Hyb & Hy1 & Hy2)]; [rewrite Hs | rewrite Hyb].
      - split; [lia|]. split; [lia|]. split; [clear - O3; unfold rw_keep in O3; Z.div_mod_to_equations; lia|].
        split; [eapply LbB_DRep.wr_at_sub; [exact (m_wrh _ _ _ _ MS) | lia | lia | lia]|].
        split; [eapply sh0_of_addressable; [exact (m_adh _ _ _ _ MS) | change (40 / 8) with 5; lia]|].
        split; [intros e He _; pose proof (node_apart_obj e He) as A; unfold apart in A; lia|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [intros C; exfalso; apply C; reflexivity|].
        pose proof OAPP as OA. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in OA |- *. lia.
      - destruct (ent_facts _ _ _ _ _ _ _ U0 Hy) as (Hy0 & Hy3 & Hy4 & _).
        pose proof (node_apart_obj y Hy) as Aoy. pose proof (HPN y Hy) as Apy. unfold apart in Aoy, Apy.
        split; [lia|]. split; [lia|]. split; [clear - Hy4; Z.div_mod_to_equations; lia|].
        split; [eapply LbB_DRep.wr_at_sub; [exact (m_wrn _ _ _ _ MS _ Hy) | lia | lia | lia]|].
        split; [eapply sh0_of_addressable; [exact (m_adn _ _ _ _ MS _ Hy) | change (32 / 8) with 4; lia]|].
        split; [intros e He Ne; pose proof (nodes_apart _ _ _ _ _ _ _ _ U0 He Hy Ne) as A; unfold apart in A; lia|].
        split; [lia|]. split; [exact (not_eq_sym Hy1)|]. split; [exact (not_eq_sym Hy2)|]. split; [intros _; lia|].
        pose proof (NAPP y Hy) as NY. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in NY |- *. lia. }
    destruct BV as (Hv0 & Hv1 & Hv8 & WRv & SHv & APv & APvb & Hvl & Hvx & Hvo & Hva).
    pose proof (APv _ Hl Hvl) as Avl. pose proof (APv _ Hx Hvx) as Avx.
    unfold ALOWSH_LO, AHI_LO in Hva.
    set (bvv := Bf (hh x)) in *. clearbody bvv. hide_mods.
    set (fx := PropExec.mkFP F fc).
    set (Eb := bn_E R S1 (addr (last P d0)) p n (hh (last P d0)) (addr x) (hh x) bvv (hdaddr S') nt).
    assert (HR : regs_ok Eb bn_sr R) by (unfold Eb, bn_E, bn_sr; rw_seedB).
    assert (HK : know_ok bsegs Eb M bn_N_knF) by (unfold Eb, bn_E; unfold rw_keep in Hx2, Hl8; knowB).
    assert (HX : Z.succ 0 = 1) by reflexivity.
    assert (FLs : sc_denot asegs M Eb (SCFlat (SA (EAlu ALU_SRL (EVar 40) (ELit 3)) SHBASE) (ELit 1))).
    { unfold Eb, bn_E. pose proof (div8_bound bvv ltac:(lia)) as D8.
      eapply (sc_flat _ _ _ _ (bvv / 8)); [evs; cbn [edenot]; rewrite HWord.w_srl by lia; change (2 ^ 3) with 8; reflexivity | lia | cbn [a_off]; unfold SHBASE; lia | lia | cbn [a_off]; unfold SHBASE; lia]. }
    assert (HS : scs_denot bsegs M Eb bn_N_scs).
    { change bsegs with asegs. unfold bn_N_scs. scs_split.
      - unfold Eb, bn_E. sc_soN HX WRv.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_shdjR HX.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_djR HX.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_djR HX.
      - unfold Eb, bn_E. unfold rw_keep in Hv8. sc_brA HX.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_brA HX.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_djR HX.
      - unfold Eb, bn_E. sc_rdR HX Cb.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_shdjR HX.
      - unfold Eb, bn_E. sc_soN HX WRx.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_djR HX.
      - unfold Eb, bn_E. sc_rdR HX Cnt.
      - unfold Eb, bn_E. sc_flatR HX bvv.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_shdjR HX.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_shdjR HX.
      - exact FLs.
      - unfold Eb, bn_E. unfold rw_keep in Hv8. sc_brA HX.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_brA HX.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_djR HX.
      - unfold Eb, bn_E. sc_rdR HX Cb.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_shdjR HX.
      - unfold Eb, bn_E. sc_soN HX WRl.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_brA HX.
      - unfold Eb, bn_E. sc_rdR HX Cb.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_brA HX.
      - unfold Eb, bn_E. clear - HX SPR' ACS Nx Nl Hx0 Hx1 Hl0 Hl1 Apx Apl Axl Hhx Hhl N5 N28 HP0 HP3 Hv0 Hv1 Hva Avl Avx Hh. sc_brA HX. }
    destruct (bn_N_run fx R M (seg_rom asegs) S1 (addr (last P d0)) p n (hh (last P d0)) (addr x) (hh x) bvv (hdaddr S') nt HS HR HK)
      as (R' & HR' & HL & Hms).
    change bsegs with asegs in Hms. unfold bn_N_ss in HR', HL, Hms. cbn [s_regs s_log s_pc] in HR', HL, Hms.
    unfold Eb in *.
    assert (KP : forall r, In r keptL -> getr R' r = getr R r) by (keptB HR HR' keptL).
    rreg_ HR' (10%bv : bv 5) H10. rreg_ HR' (17%bv : bv 5) H17.
    assert (MI' := msteps_mem_inv _ _ _ Hms (m_mi _ _ _ _ MS)). cbn [ms_mem] in MI'.
    assert (IWb : inside WL bvv 8).
    { destruct BVc as [Hs | (y & Hy & Hyb & _ & _)]; unfold WL; cbn [inside];
        [right; left; lia | right; right; rewrite Hyb; apply inside_mapN; exact Hy]. }
    assert (IWx : inside WL (addr x) 8) by (unfold WL; cbn [inside]; right; right; apply inside_mapN; exact Hx).
    assert (IWl : inside WL (addr (last P d0)) 8) by (unfold WL; cbn [inside]; right; right; apply inside_mapN; exact Hl).
    lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ (mem_denot ?EE ?m0 ?lg) _) =>
      let MM := constr:(mem_denot EE m0 lg) in
      assert (CB1 : rw_cells asegs MM bvv [C8 (Z_to_bv 64 (addr x))]) by (unfold bn_E; rwc_newR HX HL WRv);
      assert (CB2 : rw_cells asegs MM (addr x) [C8 (Z_to_bv 64 nt)]) by (unfold bn_E; rwc_newR HX HL WRx);
      assert (CB3 : rw_cells asegs MM (addr (last P d0)) [C8 (Z_to_bv 64 (hdaddr S'))]) by (unfold bn_E; rwc_newR HX HL WRl);
      assert (MU3 : munch [(bvv, bvv + 8); (addr x, addr x + 8); (addr (last P d0), addr (last P d0) + 8)] M MM)
        by (apply munch_mem_denot; [exact HL |
            repeat (apply Forall_cons; [cbn [e_addr e_width inside]; unfold estart, bn_E; evs; cbn [edenot a_base a_off]; nrmR HX;
                                        rewrite ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia |]); apply Forall_nil]);
      pose proof (wmono_mem_denot EE m0 lg) as WM;
      remember MM as M' eqn:HM'
    end.
    clear HM'.
    apply cellw8_of_rw_cells in CB1; [| lia | lia]. apply cellw8_of_rw_cells in CB2; [| lia | lia].
    apply cellw8_of_rw_cells in CB3; [| lia | lia].
    assert (MUW : munch WL M M').
    { apply (munch_widen _ M M' MU3). intros y Hy. cbn [outside].
      split; [intros Hin; exact (inside_not_outside WL bvv 8 y IWb Hin Hy)|].
      split; [intros Hin; exact (inside_not_outside WL (addr x) 8 y IWx Hin Hy)|].
      split; [intros Hin; exact (inside_not_outside WL (addr (last P d0)) 8 y IWl Hin Hy) | exact I]. }
    assert (HE' : forall a, In a (P ++ S') -> In a ents).
    { intros a Ha. apply HE. apply in_app_or in Ha. apply in_or_app. destruct Ha as [Ha | Ha]; [left; exact Ha | right; right; exact Ha]. }
    destruct (POST M' CB1 CB2 CB3) as (C1 & CH).
    { intros a Ha N1 N2 N3. pose proof (HE' a Ha) as Hae.
      destruct (ent_facts _ _ _ _ _ _ _ U0 Hae) as (Ha0 & Ha1 & _ & _).
      pose proof (nodes_apart _ _ _ _ _ _ _ _ U0 Hae Hx N2) as Aax. pose proof (nodes_apart _ _ _ _ _ _ _ _ U0 Hae Hl N1) as Aal.
      pose proof (APv a Hae N3) as Aav. unfold apart in Aax, Aal.
      apply (agree_of_munch _ M M' (addr a) 8 MU3); [| clear - Ha0; lia | clear - Ha1; lia].
      intros y Hy. cbn [outside]. clear - Hy Aax Aal Aav. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    { intros Hns. apply (agree_of_munch _ M M' (obj + 16) 8 MU3); [| clear - O1; lia | clear - O2; lia].
      pose proof (Hvo Hns) as Hvo'. intros y Hy. cbn [outside]. clear - Hy Hvo' Aox Aol. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    exists R', M', P'. split; [exact Hms|]. split; [|exact KP].
    constructor; rewrite ?KP by (unfold keptL; cbn [In]; inR); try assumption.
    - apply (msta_keep P (x :: S') Bf M M'); [exact MS | exact MUW | exact WM | exact MI' | | exact BI' | exact HP'n | exact C1 | exact CH |].
      + exact (Permutation_trans PERM' PM).
      + intros i Hi. apply (cell8_keep _ M M' _ _ MU3 (m_bkt _ _ _ _ MS i Hi)); [| clear - HP0 Hi; lia | clear - HP3 Hi ACS SPR'; lia].
        intros y Hy. cbn [outside]. clear - Hy Hi APvb Apx Apl. split; [lia|]. split; [lia|]. split; [lia | exact I].
    - rewrite H10. unfold bn_E. evs. rewrite Hlast'. reflexivity.
    - rewrite H17. unfold bn_E. evs. rewrite Hlast'. reflexivity.
  Qed.

  Lemma head_step : forall P x S' Bf M R, HSTA P x S' Bf M R ->
    exists R' M' P' Bf', CatSim.msteps asegs (st R R_HEAD M) (st R' R_LOOP M') /\ LSTA P' S' Bf' M' R'
                         /\ (forall r, In r keptL -> getr R' r = getr R r).
  Proof.
    intros P x S' Bf M R HS0.
    destruct (head_hash P x S' Bf M R HS0) as (R1 & H1 & DS & K1).
    assert (KC : forall R2, (forall r, In r keptL -> getr R2 r = getr R1 r) -> forall r, In r keptL -> getr R2 r = getr R r).
    { intros R2 K2 r Hr. rewrite (K2 r Hr). apply K1. exact (proj2 (kept_sub r Hr)). }
    destruct (Z.eq_dec (hh x) (hh (last P d0))) as [Eq | Ne].
    - destruct (disp_same P x S' Bf M R1 DS Eq) as (R2 & H2 & LS & K2).
      exists R2, M, (P ++ [x]), Bf. split; [eapply CatSim.msteps_trans; [exact H1 | exact H2] |]. split; [exact LS | exact (KC R2 K2)].
    - destruct (Z.eq_dec (Bf (hh x)) 0) as [Z0 | NZ].
      + destruct (disp_empty P x S' Bf M R1 DS Ne Z0) as (R2 & M2 & H2 & LS & K2).
        exists R2, M2, (P ++ [x]), (fun i => if i =? hh x then addr (last P d0) else Bf i).
        split; [eapply CatSim.msteps_trans; [exact H1 | exact H2] |]. split; [exact LS | exact (KC R2 K2)].
      + destruct (disp_splice P x S' Bf M R1 DS Ne NZ) as (R2 & M2 & P2 & H2 & LS & K2).
        exists R2, M2, P2, Bf. split; [eapply CatSim.msteps_trans; [exact H1 | exact H2] |]. split; [exact LS | exact (KC R2 K2)].
  Qed.
  Lemma loop_step : forall P S Bf M R x S', S = x :: S' -> LSTA P S Bf M R ->
    exists R' M' P' Bf', CatSim.msteps asegs (st R R_LOOP M) (st R' R_LOOP M') /\ LSTA P' S' Bf' M' R'
                         /\ (forall r, In r keptL -> getr R' r = getr R r).
  Proof.
    intros P S Bf M R x S' -> LS.
    destruct (loop_enter P x S' Bf M R LS) as (R1 & H1 & HS1 & K1).
    destruct (head_step P x S' Bf M R1 HS1) as (R2 & M2 & P2 & Bf2 & H2 & LS2 & K2).
    exists R2, M2, P2, Bf2. split; [eapply CatSim.msteps_trans; [exact H1 | exact H2] |]. split; [exact LS2 |].
    intros r Hr. rewrite (K2 r Hr). apply K1. exact (proj1 (kept_sub r Hr)).
  Qed.

  Lemma relink : forall S P Bf M R, LSTA P S Bf M R ->
    exists R' M' P' Bf', CatSim.msteps asegs (st R R_LOOP M) (st R' R_EXIT M') /\ MSTA P' [] Bf' M'
                         /\ (forall r, In r keptL -> getr R' r = getr R r).
  Proof.
    induction S as [|x S' IH]; intros P Bf M R LS.
    - destruct (loop_exit P Bf M R LS) as (R' & H & K). exists R', M, P, Bf.
      split; [exact H|]. split; [exact (l_m _ _ _ _ _ LS) | exact K].
    - destruct (loop_step P (x :: S') Bf M R x S' eq_refl LS) as (R1 & M1 & P1 & Bf1 & H1 & LS1 & K1).
      destruct (IH P1 Bf1 M1 R1 LS1) as (R2 & M2 & P2 & Bf2 & H2 & MS2 & K2).
      exists R2, M2, P2, Bf2. split; [eapply CatSim.msteps_trans; [exact H1 | exact H2] |]. split; [exact MS2 |].
      intros r Hr. rewrite (K2 r Hr). exact (K1 r Hr).
  Qed.

  Definition REGF (R : bvmap 5 word) : Prop :=
    getr R 9%bv = Z_to_bv 64 S1 /\ getr R 13%bv = Z_to_bv 64 (2 ^ 64 - 1 - p) /\ getr R 14%bv = Z_to_bv 64 p
    /\ getr R 27%bv = Z_to_bv 64 n /\ getr R 31%bv = Z_to_bv 64 (2 ^ 60).
  Definition REGX (R R' : bvmap 5 word) : Prop := forall r, In r keptX -> getr R' r = getr R r.

  Definition Bf1 (x : ent) : Z -> Z := fun i => if i =? hh x then sent else 0.

  Definition popcP : expr := Eval vm_compute in sr_get (s_regs pm_L_ss) 15%bv.
  Definition popcwP (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popcP.
  Lemma popcP_env : forall E, edenot E popcP = popcwP (ev E 36).
  Proof. intros E. unfold popcwP, popcP. cbn [edenot ev]. reflexivity. Qed.
  Ltac vm_popcP :=
    match goal with |- context [bv_unsigned (popcwP ?w)] =>
      let v := eval vm_compute in (bv_unsigned (popcwP w)) in
      replace (bv_unsigned (popcwP w)) with v by (vm_compute; reflexivity) end.
  Lemma popcwP_range : forall c, In c BSEQ -> 5 <= c -> 2 <= bv_unsigned (popcwP (Z_to_bv 64 c)) <= 64.
  Proof.
    intros c Hin Hc. unfold BSEQ in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [exfalso; lia | vm_popcP; lia] |]).
    destruct Hin.
  Qed.

  Lemma pro_mem : forall x S M', ents = x :: S ->
    cell8 ASEGS ML sent (hdaddr ents) -> chain ASEGS ML ents -> (forall e, In e ents -> cell8 ASEGS ML (addr e + 8) (hkey e)) ->
    (forall i, 0 <= i < n -> cell8 ASEGS ML (p + 8 * i) 0) ->
    addressable ML p (8 * n) -> addressable ML obj 40 -> (forall e, In e ents -> addressable ML (addr e) 32) ->
    wr_at asegs ML p (8 * n) -> wr_at asegs ML obj 40 -> (forall e, In e ents -> wr_at asegs ML (addr e) 32) ->
    munch [(p + 8 * hh x, p + 8 * hh x + 8)] ML M' -> wmono asegs ML M' -> mem_inv asegs M' ->
    cell8 ASEGS M' (p + 8 * hh x) sent ->
    MSTA [x] S (Bf1 x) M'.
  Proof.
    intros x S M' E0 C1 CH HKs BK ADP ADH ADN WRP WRH WRN MU WM MI' CB.
    pose proof SPR as SPR'. pose proof ACS as ACS'. pose proof HP as (HP0 & HP1 & HP2 & HP3 & HPa).
    pose proof HPO as HPO'. unfold apart in HPO'. pose proof (u_obj_lo U0) as O1. pose proof (u_obj_hi U0) as O2.
    pose proof n_factsL as (_ & _ & N28 & _).
    pose proof (hh_lt x) as Hhx.
    assert (OUTB : forall a k, 0 <= a -> (a + k <= p \/ p + 8 * n <= a) -> forall y, a <= y < a + k ->
                   outside [(p + 8 * hh x, p + 8 * hh x + 8)] y).
    { intros a k Ha Hak y Hy. cbn [outside]. split; [lia | exact I]. }
    assert (MUW : munch WL ML M').
    { apply (munch_widen _ ML M' MU). intros y Hy. unfold WL in Hy. cbn [outside] in Hy |- *.
      destruct Hy as (Hy1 & _). split; [lia | exact I]. }
    constructor.
    - rewrite E0. apply Permutation_refl.
    - unfold Bf1. eapply HRehashModel.binv_start; lia.
    - discriminate.
    - cbn [app]. rewrite E0 in C1.
      apply (cell8_keep _ ML M' _ _ MU C1); [intros y Hy; apply (OUTB (obj + 16) 8 ltac:(lia) ltac:(lia) y Hy) | lia | lia].
    - cbn [app]. rewrite <- E0. eapply chain_agree; [exact CH |]. intros q k v Hq.
      destruct (ent_facts _ _ _ _ _ _ _ U0 Hq) as (Hq0 & Hq1 & _ & _). pose proof (HPN _ Hq) as Aq.
      unfold apart in Aq. cbn [HRehashModel.addr fst] in Aq, Hq0, Hq1.
      split; [| lia]. apply (agree_of_munch _ ML M' q 8 MU); [| lia | lia].
      intros y Hy. apply (OUTB q 8 ltac:(lia) ltac:(lia) y Hy).
    - intros e He. destruct (ent_facts _ _ _ _ _ _ _ U0 He) as (He0 & He1 & _ & _). pose proof (HPN e He) as Ae. unfold apart in Ae.
      apply (cell8_keep _ ML M' _ _ MU (HKs e He)); [intros y Hy; apply (OUTB (addr e + 8) 8 ltac:(lia) ltac:(lia) y Hy) | lia | lia].
    - intros i Hi. unfold Bf1. destruct (Z.eqb_spec i (hh x)) as [-> | Hne]; [exact CB |].
      apply (cell8_keep _ ML M' _ _ MU (BK i Hi)); [| lia | lia].
      intros y Hy. cbn [outside]. split; [lia | exact I].
    - apply (adr_keep ML); [exact MUW | exact ADP | lia | lia].
    - apply (adr_keep ML); [exact MUW | exact ADH | lia | lia].
    - intros e He. destruct (ent_facts _ _ _ _ _ _ _ U0 He) as (He0 & He1 & _ & _).
      apply (adr_keep ML); [exact MUW | exact (ADN e He) | lia | lia].
    - exact MUW.
    - exact WM.
    - exact MI'.
    - exact (wr_keep _ _ _ _ WM WRP).
    - exact (wr_keep _ _ _ _ WM WRH).
    - intros e He. exact (wr_keep _ _ _ _ WM (WRN e He)).
    - eapply rw_cells_transport; [exact S616L | exact MU | exact WM |].
      cbn [disjoint_from]. split; [| exact I]. change (Z.of_nat (cells_size [C8 (Z_to_bv 64 SHBASE)])) with 8.
      clear - SPR' ACS' HP3 Hhx. lia.
  Qed.

  Lemma pro_emp : forall R, REGF R -> ents = [] -> cell8 ASEGS ML sent (hdaddr ents) -> addressable ML obj 40 -> mem_inv asegs ML ->
    exists R', CatSim.msteps asegs (st R R_MS ML) (st R' R_EXIT ML) /\ REGX R R'.
  Proof.
    intros R RF E0 C1 ADH MI. rewrite E0 in C1. cbn [hdaddr] in C1.
    destruct RF as (X9 & X13 & X14 & X27 & X31).
    pose proof SPR as SPR'. pose proof ACS as ACS'. pose proof OCE as OCE'.
    pose proof HP as (HP0 & HP1 & HP2 & HP3 & _). unfold AIMG_TOP in HP2.
    pose proof OAPP as OA. unfold aapp, aapp_lo, aapp_hi, AHI_LO, AIMG_TOP in OA.
    pose proof n_factsL as (HnB & Hbcn & N28 & Hbc0).
    assert (N2 : 2 <= n).
    { clear - HnB Hbcn Hbc0. unfold BSEQ in HnB. repeat (destruct HnB as [HnB | HnB]; [lia |]). destruct HnB. }
    assert (F616 : fldA ML (S1 + 616) 8 SHBASE) by (apply fld_of_slot; [exact S616L | unfold SHBASE; lia | lia]).
    assert (F648 : fldA ML (S1 + 648) 8 (obj - 136)) by (apply fld_of_slot; [exact S648L | lia | lia]).
    assert (F0 : fldA ML (obj + 16) 8 0) by (apply fld_of_cell8; exact C1).
    assert (SH : sh0 ML (obj + 16)) by (eapply sh0_of_addressable; [exact ADH | change (40 / 8) with 5; lia]).
    set (fx := PropExec.mkFP F fc).
    assert (HR : regs_ok (pe_E R S1 p n 0 0 (obj - 136) (2 ^ 64 - 1 - p) 0) pe_sr R) by (unfold pe_E, pe_sr; rw_seedB).
    assert (HK : know_ok bsegs (pe_E R S1 p n 0 0 (obj - 136) (2 ^ 64 - 1 - p) 0) ML pe_E_knF) by (unfold pe_E; knowB).
    assert (HS : scs_denot bsegs ML (pe_E R S1 p n 0 0 (obj - 136) (2 ^ 64 - 1 - p) 0) pe_E_scs) by (unfold pe_E_scs; split_scs).
    destruct (pe_E_run fx R ML (seg_rom asegs) S1 p n 0 0 (obj - 136) (2 ^ 64 - 1 - p) 0 HS HR HK) as (R' & HR' & HL & Hms).
    change bsegs with asegs in Hms. unfold pe_E_ss in HR', HL, Hms. cbn [s_regs s_log s_pc mem_denot] in HR', HL, Hms.
    exists R'. split; [exact Hms | unfold REGX; keptB HR HR' keptX].
  Qed.

  Lemma pro_one : forall R x, REGF R -> ents = [x] ->
    cell8 ASEGS ML sent (hdaddr ents) -> chain ASEGS ML ents -> (forall e, In e ents -> cell8 ASEGS ML (addr e + 8) (hkey e)) ->
    addressable ML p (8 * n) -> addressable ML obj 40 -> (forall e, In e ents -> addressable ML (addr e) 32) ->
    mem_inv asegs ML -> wr_at asegs ML p (8 * n) ->
    exists R' M', CatSim.msteps asegs (st R R_MS ML) (st R' R_EXIT M') /\ REGX R R'
      /\ munch [(p + 8 * hh x, p + 8 * hh x + 8)] ML M' /\ wmono asegs ML M' /\ mem_inv asegs M'
      /\ cell8 ASEGS M' (p + 8 * hh x) sent.
  Proof.
    intros R x RF E0 C1 CH HKs ADP ADH ADN MI WRP.
    assert (C1x : cell8 ASEGS ML sent (addr x)) by (rewrite E0 in C1; destruct x as [xa [xk xv]]; exact C1).
    destruct RF as (X9 & X13 & X14 & X27 & X31).
    assert (Hx : In x ents) by (rewrite E0; left; reflexivity).
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hx) as (Hx0 & Hx1 & Hx2 & Hk).
    assert (Hne : ents <> []) by (rewrite E0; discriminate).
    pose proof (n_ge5 Hne) as N5. pose proof n_factsL as (HnB & Hbcn & N28 & Hbc0).
    pose proof (hh_lt x) as Hhx.
    pose proof SPR as SPR'. pose proof ACS as ACS'. pose proof OCE as OCE'.
    pose proof HP as (HP0 & HP1 & HP2 & HP3 & HPa). unfold AIMG_TOP in HP2.
    pose proof OAPP as OA. unfold aapp, aapp_lo, aapp_hi, AHI_LO, AIMG_TOP in OA.
    pose proof HPO as HPO'. unfold apart in HPO'.
    pose proof (HPN x Hx) as Apx. unfold apart in Apx.
    pose proof (NAPP x Hx) as Nx. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in Nx.
    pose proof HPa as HPa'. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in HPa'.
    assert (F616 : fldA ML (S1 + 616) 8 SHBASE) by (apply fld_of_slot; [exact S616L | unfold SHBASE; lia | lia]).
    assert (F648 : fldA ML (S1 + 648) 8 (obj - 136)) by (apply fld_of_slot; [exact S648L | lia | lia]).
    assert (F0 : fldA ML (obj + 16) 8 (addr x)) by (apply fld_of_cell8; exact C1x).
    assert (F8 : fldA ML (addr x + 8) 8 (hkey x)) by (apply fld_of_cell8; exact (HKs x Hx)).
    assert (FN : fldA ML (addr x) 8 0).
    { apply fld_of_cell8. pose proof (chain_last_nil ML [x] ltac:(rewrite <- E0; exact CH) ltac:(discriminate)) as CL.
      cbn [last] in CL. exact CL. }
    assert (SHo : sh0 ML (obj + 16)) by (eapply sh0_of_addressable; [exact ADH | change (40 / 8) with 5; lia]).
    assert (SHx : sh0 ML (addr x)) by (eapply sh0_of_addressable; [exact (ADN x Hx) | change (32 / 8) with 4; lia]).
    assert (SHx8 : sh0 ML (addr x + 8)) by (eapply sh0_of_addressable; [exact (ADN x Hx) | change (32 / 8) with 4; lia]).
    assert (SHB : sh0 ML (p + 8 * hh x)).
    { eapply sh0_of_addressable; [exact ADP |]. rewrite (Z.mul_comm 8 n), Z.div_mul by lia. lia. }
    assert (WRb : wr_at asegs ML (p + 8 * hh x) 8) by (eapply LbB_DRep.wr_at_sub; [exact WRP | lia | lia | lia]).
    assert (HX : Z.succ 0 = 1) by reflexivity.
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot (ps_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0) (ELit 1))
                     (edenot (ps_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0) popcP) = b ->
                   sc_denot asegs ML (ps_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0) (SCBr b BC_LTU (ELit 1) popcP))
      by (intros b Hb; exact Hb).
    pose proof (popcwP_range n HnB ltac:(lia)) as PR.
    set (fx := PropExec.mkFP F fc).
    assert (HR : regs_ok (ps_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0) ps_sr R) by (unfold ps_E, ps_sr; rw_seedB).
    destruct (Z_lt_ge_dec (hkey x) n) as [Hlt | Hge];
      [ assert (Hhh : hh x = hkey x) by (unfold HRehashModel.hh, hmod; apply Z.mod_small; lia)
      | assert (Hhh : hh x = hkey x mod n) by (unfold HRehashModel.hh, hmod; reflexivity) ];
      rewrite Hhh in SHB, WRb, Hhx |- *.
    - assert (HK : know_ok bsegs (ps_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0) ML ps_L_knF)
        by (unfold ps_E; knowB).
      assert (HS : scs_denot bsegs ML (ps_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0) ps_L_scs).
      { change bsegs with asegs. unfold ps_L_scs, ps_E. scs_split.
        - clear - HX SPR' ACS' HP0 HP3 Hx0 Hx1 Apx Hhx N28 N5 Nx HPa'; sc_djR HX.
        - clear - HX SPR' ACS' HP0 HP3 Hx0 Hx1 Apx Hhx N28 N5 Nx HPa'; sc_shdjR HX.
        - sc_soN HX WRb.
        - sc_brR HX.
        - apply Hpc; rewrite popcP_env; replace (ev (ps_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0) 36) with (Z_to_bv 64 n) by (unfold ps_E; evs; reflexivity); evs; rewrite (branch_ltu_lit_l _ 1) by lia; apply Z.ltb_lt; clear - PR; lia. }
      destruct (ps_L_run fx R ML (seg_rom asegs) S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0 HS HR HK)
        as (R' & HR' & HL & Hms).
      change bsegs with asegs in Hms. unfold ps_L_ss in HR', HL, Hms. cbn [s_regs s_log s_pc] in HR', HL, Hms.
      pose proof (munch_log _ ML _ HL) as MUL.
      assert (MI' := msteps_mem_inv _ _ _ Hms MI). cbn [ms_mem] in MI'.
      lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ (mem_denot ?EE ?m0 ?lg) _) =>
        let MM := constr:(mem_denot EE m0 lg) in
        assert (CB : rw_cells asegs MM (p + 8 * hkey x) [C8 (Z_to_bv 64 (obj - 136 + 152))]) by (unfold ps_E; rwc_newR HX HL WRb);
        assert (MU1 : munch [(p + 8 * hkey x, p + 8 * hkey x + 8)] ML MM) by (eapply munch_eqW; [exact MUL |];
          unfold log_ivs; cbn [map e_addr e_width]; unfold estart, ps_E; evs; cbn [edenot a_base a_off]; nrmR HX;
          rewrite ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat]; f_equal; f_equal; lia);
        pose proof (wmono_mem_denot EE m0 lg) as WM;
        remember MM as M' eqn:HM'
      end.
      clear HM'.
      replace (obj - 136 + 152) with (obj + 16) in CB by lia.
      apply cellw8_of_rw_cells in CB; [| lia | lia].
      exists R', M'. split; [exact Hms|]. split; [unfold REGX; keptB HR HR' keptX|].
      split; [exact MU1|]. split; [exact WM|]. split; [exact MI'|]. exact CB.
    - assert (SHB' : sh0 ML (p + 8 * (hkey x mod n))) by exact SHB.
      assert (WRb' : wr_at asegs ML (p + 8 * (hkey x mod n)) 8) by exact WRb.
      pose proof (Z.mod_pos_bound (hkey x) n ltac:(lia)) as Hmn.
      assert (HK : know_ok bsegs (ps_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0) ML ps_G_knF).
      { unfold ps_E. change bsegs with asegs. kn_eval. unfold know_ok.
        repeat (apply Forall_cons;
          [ first [ kentryB
                  | eapply (rw_kw_sh0 _ ML _ (p + 8 * (hkey x mod n)));
                    [ evs; rewrite w_remu by lia; rewrite w_mul by lia; rewrite w_add by lia; reflexivity | lia | exact SHB' ] ] |]).
        apply Forall_nil. }
      assert (HS : scs_denot bsegs ML (ps_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0) ps_G_scs).
      { change bsegs with asegs. unfold ps_G_scs, ps_E. scs_split.
        - clear - HX SPR' ACS' HP0 HP3 Hx0 Hx1 Apx Hhx N28 N5 Nx HPa' Hmn Hk; sc_djR HX.
        - clear - HX SPR' ACS' HP0 HP3 Hx0 Hx1 Apx Hhx N28 N5 Nx HPa' Hmn Hk; sc_shdjR HX.
        - sc_soN HX WRb.
        - eapply (sc_flat _ _ _ _ (p + 8 * (hkey x mod n)));
          [ evs; cbn [edenot]; rewrite w_remu by lia; rewrite w_mul by lia; rewrite w_add by lia; reflexivity
          | clear - HP0 HP3 Hmn ACS' SPR'; lia | cbn [a_off]; clear - HP0 HP3 Hmn ACS' SPR'; lia | lia
          | cbn [a_off]; clear - HP0 HP3 Hmn ACS' SPR'; lia ].
        - pose proof (div8_bound (p + 8 * (hkey x mod n)) ltac:(clear - HP0 HP3 Hmn ACS' SPR'; lia)) as D8.
          eapply (sc_flat _ _ _ _ ((p + 8 * (hkey x mod n)) / 8));
          [ evs; cbn [edenot]; rewrite w_remu by lia; rewrite w_mul by lia; rewrite w_add by lia;
            rewrite HWord.w_srl by (clear - HP0 HP3 Hmn ACS' SPR'; lia); change (2 ^ 3) with 8; reflexivity
          | lia | cbn [a_off]; unfold SHBASE; lia | lia | cbn [a_off]; unfold SHBASE; lia ].
        - sc_brR HX.
        - sc_brR HX.
        - apply Hpc; rewrite popcP_env; replace (ev (ps_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0) 36) with (Z_to_bv 64 n) by (unfold ps_E; evs; reflexivity); evs; rewrite (branch_ltu_lit_l _ 1) by lia; apply Z.ltb_lt; clear - PR; lia. }
      destruct (ps_G_run fx R ML (seg_rom asegs) S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) 0 HS HR HK)
        as (R' & HR' & HL & Hms).
      change bsegs with asegs in Hms. unfold ps_G_ss in HR', HL, Hms. cbn [s_regs s_log s_pc] in HR', HL, Hms.
      pose proof (munch_log _ ML _ HL) as MUL.
      assert (MI' := msteps_mem_inv _ _ _ Hms MI). cbn [ms_mem] in MI'.
      lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ (mem_denot ?EE ?m0 ?lg) _) =>
        let MM := constr:(mem_denot EE m0 lg) in
        assert (CB : rw_cells asegs MM (p + 8 * (hkey x mod n)) [C8 (Z_to_bv 64 (obj - 136 + 152))]) by (unfold ps_E; rwc_newR HX HL WRb);
        assert (MU1 : munch [(p + 8 * (hkey x mod n), p + 8 * (hkey x mod n) + 8)] ML MM) by (eapply munch_eqW; [exact MUL |];
          unfold log_ivs; cbn [map e_addr e_width]; unfold estart, ps_E; evs; cbn [edenot a_base a_off]; nrmR HX;
          rewrite ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat]; f_equal; f_equal; lia);
        pose proof (wmono_mem_denot EE m0 lg) as WM;
        remember MM as M' eqn:HM'
      end.
      clear HM'.
      replace (obj - 136 + 152) with (obj + 16) in CB by lia.
      apply cellw8_of_rw_cells in CB; [| lia | lia].
      exists R', M'. split; [exact Hms|]. split; [unfold REGX; keptB HR HR' keptX|].
      split; [exact MU1|]. split; [exact WM|]. split; [exact MI'|]. exact CB.
  Qed.

  Lemma popc_br : forall M E, ev E 36 = Z_to_bv 64 n -> 5 <= n -> sc_denot asegs M E (SCBr true BC_LTU (ELit 1) popcP).
  Proof.
    intros M E H36 N5. cbn [sc_denot]. rewrite popcP_env, H36. cbn [edenot].
    pose proof n_factsL as (HnB & _ & _ & _).
    pose proof (popcwP_range n HnB N5) as PR.
    set (u := popcwP (Z_to_bv 64 n)) in *. clearbody u.
    rewrite <- (Z_to_bv_bv_unsigned u). rewrite br_ltu by lia. apply Z.ltb_lt. lia.
  Qed.

  Lemma popc_rng : forall E, ev E 36 = Z_to_bv 64 n -> 5 <= n -> 2 <= bv_unsigned (edenot E popcP) <= 64.
  Proof.
    intros E H36 N5. rewrite popcP_env, H36.
    pose proof n_factsL as (HnB & _ & _ & _). exact (popcwP_range n HnB N5).
  Qed.

  Lemma pro_many : forall R x y S, REGF R -> ents = x :: y :: S ->
    cell8 ASEGS ML sent (hdaddr ents) -> chain ASEGS ML ents -> (forall e, In e ents -> cell8 ASEGS ML (addr e + 8) (hkey e)) ->
    addressable ML p (8 * n) -> addressable ML obj 40 -> (forall e, In e ents -> addressable ML (addr e) 32) ->
    mem_inv asegs ML -> wr_at asegs ML p (8 * n) ->
    exists R' M', CatSim.msteps asegs (st R R_MS ML) (st R' R_HEAD M') /\ REGX R R'
      /\ munch [(p + 8 * hh x, p + 8 * hh x + 8)] ML M' /\ wmono asegs ML M' /\ mem_inv asegs M'
      /\ cell8 ASEGS M' (p + 8 * hh x) sent
      /\ getr R' 5%bv = Z_to_bv 64 1 /\ getr R' 10%bv = Z_to_bv 64 (addr x) /\ getr R' 11%bv = Z_to_bv 64 (addr y)
      /\ 2 <= bv_unsigned (getr R' 15%bv) <= 64 /\ getr R' 17%bv = Z_to_bv 64 (hh x) /\ getr R' 29%bv = Z_to_bv 64 SHBASE.
  Proof.
    intros R x y S RF E0 C1 CH HKs ADP ADH ADN MI WRP.
    destruct RF as (X9 & X13 & X14 & X27 & X31).
    assert (Hx : In x ents) by (rewrite E0; left; reflexivity).
    assert (Hy : In y ents) by (rewrite E0; right; left; reflexivity).
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hx) as (Hx0 & Hx1 & Hx2 & Hk).
    destruct (ent_facts _ _ _ _ _ _ _ U0 Hy) as (Hy0 & Hy1 & Hy2 & _).
    assert (Hne : ents <> []) by (rewrite E0; discriminate).
    pose proof (n_ge5 Hne) as N5. pose proof n_factsL as (HnB & Hbcn & N28 & Hbc0).
    pose proof SPR as SPR'. pose proof ACS as ACS'. pose proof OCE as OCE'.
    pose proof HP as (HP0 & HP1 & HP2 & HP3 & HPa). unfold AIMG_TOP in HP2.
    unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in HPa.
    pose proof OAPP as OA. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in OA.
    pose proof (NAPP x Hx) as NX. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in NX.
    pose proof HPO as HPO'. unfold apart in HPO'. pose proof (HPN x Hx) as HPX. unfold apart in HPX.
    pose proof (node_apart_obj x Hx) as AOX. unfold apart in AOX.
    rewrite E0 in C1. cbn [hdaddr] in C1.
    assert (F616 : fldA ML (S1 + 616) 8 SHBASE) by (apply fld_of_slot; [exact S616L | unfold SHBASE; lia | lia]).
    assert (F648 : fldA ML (S1 + 648) 8 (obj - 136)) by (apply fld_of_slot; [exact S648L | lia | lia]).
    assert (F0 : fldA ML (obj + 16) 8 (addr x)) by (apply fld_of_cell8; exact C1).
    assert (F8 : fldA ML (addr x + 8) 8 (hkey x)) by (apply fld_of_cell8; exact (HKs x Hx)).
    assert (FN : fldA ML (addr x) 8 (addr y)).
    { apply fld_of_cell8. rewrite E0 in CH. pose proof (chain_head_next ML [] x (y :: S) CH) as CN.
      cbn [hdaddr] in CN. exact CN. }
    assert (SHO : sh0 ML (obj + 16)) by (eapply sh0_of_addressable; [exact ADH | change (40 / 8) with 5; lia]).
    assert (SHX8 : sh0 ML (addr x + 8)) by (eapply sh0_of_addressable; [exact (ADN x Hx) | change (32 / 8) with 4; lia]).
    assert (SHX : sh0 ML (addr x)) by (eapply sh0_of_addressable; [exact (ADN x Hx) | change (32 / 8) with 4; lia]).
    set (fx := PropExec.mkFP F fc).
    assert (HR : regs_ok (pm_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) (addr y)) pm_sr R)
      by (unfold pm_E, pm_sr; rw_seedB).
    assert (HX : Z.succ 0 = 1) by reflexivity.
    assert (E36 : ev (pm_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) (addr y)) 36 = Z_to_bv 64 n)
      by (unfold pm_E; evs; reflexivity).
    destruct (Z_lt_ge_dec (hkey x) n) as [Hlt | Hge].
    - assert (HH : hh x = hkey x) by (unfold HRehashModel.hh, hmod; rewrite Z.mod_small by lia; reflexivity).
      rewrite HH.
      assert (SHB : sh0 ML (p + 8 * hkey x)).
      { eapply sh0_of_addressable; [exact ADP |]. rewrite (Z.mul_comm 8 n), Z.div_mul by lia. lia. }
      assert (WRb : wr_at asegs ML (p + 8 * hkey x) 8) by (eapply LbB_DRep.wr_at_sub; [exact WRP | lia | lia | lia]).
      assert (HK : know_ok bsegs (pm_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) (addr y)) ML pm_L_knF)
        by (unfold pm_E; knowB).
      assert (HS : scs_denot bsegs ML (pm_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) (addr y)) pm_L_scs).
      { change bsegs with asegs. unfold pm_L_scs. scs_split.
        - unfold pm_E. sc_djR HX.
        - unfold pm_E. sc_djR HX.
        - unfold pm_E. sc_shdjR HX.
        - unfold pm_E. sc_soN HX WRP.
        - unfold pm_E. sc_brR HX.
        - apply popc_br; [exact E36 | exact N5]. }
      destruct (pm_L_run fx R ML (seg_rom asegs) S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) (addr y) HS HR HK)
        as (R' & HR' & HL & Hms).
      change bsegs with asegs in Hms. unfold pm_L_ss in HR', HL, Hms. cbn [s_regs s_log s_pc] in HR', HL, Hms.
      assert (KP : REGX R R') by (unfold REGX; keptB HR HR' keptX).
      rreg_ HR' (5%bv : bv 5) H5. rreg_ HR' (10%bv : bv 5) H10. rreg_ HR' (11%bv : bv 5) H11.
      rreg_ HR' (15%bv : bv 5) H15. rreg_ HR' (17%bv : bv 5) H17. rreg_ HR' (29%bv : bv 5) H29.
      pose proof (munch_log _ ML _ HL) as MUL.
      assert (MI' := msteps_mem_inv _ _ _ Hms MI). cbn [ms_mem] in MI'.
      lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ (mem_denot ?EE ?m0 ?lg) _) =>
        let MM := constr:(mem_denot EE m0 lg) in
        assert (CB : rw_cells asegs MM (p + 8 * hkey x) [C8 (Z_to_bv 64 (obj - 136 + 152))]) by (unfold pm_E; rwc_newR HX HL WRb);
        assert (MU1 : munch [(p + 8 * hkey x, p + 8 * hkey x + 8)] ML MM) by (eapply munch_eqW; [exact MUL |];
          unfold log_ivs; cbn [map e_addr e_width]; unfold estart, pm_E; evs; cbn [edenot a_base a_off]; nrmR HX;
          rewrite ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat]; f_equal; f_equal; lia);
        pose proof (wmono_mem_denot EE m0 lg) as WM;
        remember MM as M' eqn:HM'
      end.
      clear HM'.
      replace (obj - 136 + 152) with (obj + 16) in CB by ring.
      apply cellw8_of_rw_cells in CB; [| lia | lia].
      exists R', M'. split; [exact Hms|]. split; [exact KP|]. split; [exact MU1|]. split; [exact WM|].
      split; [exact MI'|]. split; [exact CB|].
      split; [rewrite H5; reflexivity|].
      split; [rewrite H10; unfold pm_E; evs; reflexivity|].
      split; [rewrite H11; unfold pm_E; evs; reflexivity|].
      split; [rewrite H15; apply popc_rng; [exact E36 | exact N5]|].
      split; [rewrite H17; unfold pm_E; evs; reflexivity|].
      rewrite H29. reflexivity.
    - assert (HH : hh x = hkey x mod n) by (unfold HRehashModel.hh, hmod; reflexivity).
      rewrite HH.
      assert (HMB : 0 <= hkey x mod n < n) by (apply Z.mod_pos_bound; lia).
      assert (SHB : sh0 ML (p + 8 * (hkey x mod n))).
      { eapply sh0_of_addressable; [exact ADP |]. rewrite (Z.mul_comm 8 n), Z.div_mul by lia. lia. }
      assert (WRb : wr_at asegs ML (p + 8 * (hkey x mod n)) 8) by (eapply LbB_DRep.wr_at_sub; [exact WRP | lia | lia | lia]).
      pose proof (div8_bound (p + 8 * (hkey x mod n)) ltac:(lia)) as D8.
      assert (HK : know_ok bsegs (pm_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) (addr y)) ML pm_G_knF).
      { unfold pm_E. change bsegs with asegs. kn_eval. unfold know_ok.
        repeat (apply Forall_cons; [first [kentryB
          | eapply (rw_kw_sh0 _ _ _ (p + 8 * (hkey x mod n)));
            [evs; cbn [edenot]; nrmR HX; first [reflexivity | f_equal; lia] | lia | exact SHB]] |]).
        apply Forall_nil. }
      assert (HS : scs_denot bsegs ML (pm_E R S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) (addr y)) pm_G_scs).
      { change bsegs with asegs. unfold pm_G_scs. scs_split.
        - unfold pm_E. sc_djR HX.
        - unfold pm_E. sc_djR HX.
        - unfold pm_E. sc_shdjR HX.
        - unfold pm_E. sc_soN HX WRP.
        - unfold pm_E. eapply (sc_flat _ _ _ _ (p + 8 * (hkey x mod n)));
            [evs; cbn [edenot]; nrmR HX; first [reflexivity | f_equal; lia] | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia].
        - unfold pm_E. eapply (sc_flat _ _ _ _ ((p + 8 * (hkey x mod n)) / 8));
            [evs; cbn [edenot]; nrmR HX; rewrite HWord.w_srl by lia; change (2 ^ 3) with 8; reflexivity
            | lia | cbn [a_off]; unfold SHBASE; lia | lia | cbn [a_off]; unfold SHBASE; lia].
        - unfold pm_E. sc_brR HX.
        - unfold pm_E. sc_brR HX.
        - apply popc_br; [exact E36 | exact N5]. }
      destruct (pm_G_run fx R ML (seg_rom asegs) S1 p n (addr x) (hkey x) (obj - 136) (2 ^ 64 - 1 - p) (addr y) HS HR HK)
        as (R' & HR' & HL & Hms).
      change bsegs with asegs in Hms. unfold pm_G_ss in HR', HL, Hms. cbn [s_regs s_log s_pc] in HR', HL, Hms.
      assert (KP : REGX R R') by (unfold REGX; keptB HR HR' keptX).
      rreg_ HR' (5%bv : bv 5) H5. rreg_ HR' (10%bv : bv 5) H10. rreg_ HR' (11%bv : bv 5) H11.
      rreg_ HR' (15%bv : bv 5) H15. rreg_ HR' (17%bv : bv 5) H17. rreg_ HR' (29%bv : bv 5) H29.
      pose proof (munch_log _ ML _ HL) as MUL.
      assert (MI' := msteps_mem_inv _ _ _ Hms MI). cbn [ms_mem] in MI'.
      lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ (mem_denot ?EE ?m0 ?lg) _) =>
        let MM := constr:(mem_denot EE m0 lg) in
        assert (CB : rw_cells asegs MM (p + 8 * (hkey x mod n)) [C8 (Z_to_bv 64 (obj - 136 + 152))]) by (unfold pm_E; rwc_newR HX HL WRb);
        assert (MU1 : munch [(p + 8 * (hkey x mod n), p + 8 * (hkey x mod n) + 8)] ML MM) by (eapply munch_eqW; [exact MUL |];
          unfold log_ivs; cbn [map e_addr e_width]; unfold estart, pm_E; evs; cbn [edenot a_base a_off]; nrmR HX;
          rewrite ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat]; f_equal; f_equal; lia);
        pose proof (wmono_mem_denot EE m0 lg) as WM;
        remember MM as M' eqn:HM'
      end.
      clear HM'.
      replace (obj - 136 + 152) with (obj + 16) in CB by ring.
      apply cellw8_of_rw_cells in CB; [| lia | lia].
      exists R', M'. split; [exact Hms|]. split; [exact KP|]. split; [exact MU1|]. split; [exact WM|].
      split; [exact MI'|]. split; [exact CB|].
      split; [rewrite H5; reflexivity|].
      split; [rewrite H10; unfold pm_E; evs; reflexivity|].
      split; [rewrite H11; unfold pm_E; evs; reflexivity|].
      split; [rewrite H15; apply popc_rng; [exact E36 | exact N5]|].
      split; [rewrite H17; unfold pm_E; evs; rewrite w_remu by lia; reflexivity|].
      rewrite H29. reflexivity.
  Qed.

  Lemma loop_all : forall R, REGF R ->
    cell8 ASEGS ML sent (hdaddr ents) -> chain ASEGS ML ents -> (forall e, In e ents -> cell8 ASEGS ML (addr e + 8) (hkey e)) ->
    (forall i, 0 <= i < n -> cell8 ASEGS ML (p + 8 * i) 0) ->
    addressable ML p (8 * n) -> addressable ML obj 40 -> (forall e, In e ents -> addressable ML (addr e) 32) ->
    mem_inv asegs ML -> wr_at asegs ML p (8 * n) -> wr_at asegs ML obj 40 -> (forall e, In e ents -> wr_at asegs ML (addr e) 32) ->
    exists R' M', CatSim.msteps asegs (st R R_MS ML) (st R' R_EXIT M') /\ REGX R R'
      /\ ((ents = [] /\ M' = ML) \/ (exists P' Bf', MSTA P' [] Bf' M')).
  Proof.
    intros R RF C1 CH HKs BK ADP ADH ADN MI WRP WRH WRN.
    assert (Hc : forall l : list ent, l = [] \/ (exists x, l = [x]) \/ exists x y S, l = x :: y :: S)
      by (intros [|x [|y S]]; [left | right; left; exists x | right; right; exists x, y, S]; reflexivity).
    destruct (Hc ents) as [E0 | [(x & E0) | (x & y & S & E0)]].
    - destruct (pro_emp R RF E0 C1 ADH MI) as (R' & H1 & X1).
      exists R', ML. split; [exact H1|]. split; [exact X1|]. left. split; [exact E0 | reflexivity].
    - destruct (pro_one R x RF E0 C1 CH HKs ADP ADH ADN MI WRP) as (R' & M' & H1 & X1 & MU & WM & MI' & CB).
      exists R', M'. split; [exact H1|]. split; [exact X1|]. right. exists [x], (Bf1 x).
      exact (pro_mem x [] M' E0 C1 CH HKs BK ADP ADH ADN WRP WRH WRN MU WM MI' CB).
    - destruct (pro_many R x y S RF E0 C1 CH HKs ADP ADH ADN MI WRP)
        as (R1 & M1 & H1 & X1 & MU & WM & MI1 & CB & G5 & G10 & G11 & G15 & G17 & G29).
      pose proof (pro_mem x (y :: S) M1 E0 C1 CH HKs BK ADP ADH ADN WRP WRH WRN MU WM MI1 CB) as MS1.
      pose proof RF as (F9 & F13 & F14 & F27 & F31).
      assert (KX : forall r, In r keptX -> getr R1 r = getr R r) by exact X1.
      assert (HS1 : HSTA [x] y S (Bf1 x) M1 R1).
      { constructor; [exact MS1 | exact G5 | | exact G10 | exact G11 | | exact G15 | exact G17 | | exact G29 |].
        - rewrite KX by (unfold keptX; cbn [In]; inR). exact F9.
        - rewrite KX by (unfold keptX; cbn [In]; inR). exact F14.
        - rewrite KX by (unfold keptX; cbn [In]; inR). exact F27.
        - rewrite KX by (unfold keptX; cbn [In]; inR). exact F31. }
      destruct (head_step [x] y S (Bf1 x) M1 R1 HS1) as (R2 & M2 & P2 & Bf2 & H2 & LS2 & K2).
      destruct (relink S P2 Bf2 M2 R2 LS2) as (R3 & M3 & P3 & Bf3 & H3 & MS3 & K3).
      exists R3, M3. split; [eapply CatSim.msteps_trans; [exact H1 | eapply CatSim.msteps_trans; [exact H2 | exact H3]]|].
      split; [| right; exists P3, Bf3; exact MS3].
      intros r Hr. rewrite (K3 r (keptX_sub r Hr)), (K2 r (keptX_sub r Hr)). exact (KX r Hr).
  Qed.
End NtRL.
