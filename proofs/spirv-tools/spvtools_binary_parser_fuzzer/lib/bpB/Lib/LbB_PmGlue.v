(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps BW_MallocBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require SeqExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Fixpoint rt_lookup (RT : list (reg * expr)) (r : reg) : option expr :=
  match RT with
  | [] => None
  | (r', e) :: RT' => if bv_eqb r' r then Some e else rt_lookup RT' r
  end.

Lemma rt_lookup_in : forall RT r e, rt_lookup RT r = Some e -> In (r, e) RT.
Proof.
  induction RT as [|[r' e'] RT IH]; intros r e Hl; cbn [rt_lookup] in Hl; [discriminate|].
  destruct (bv_eqb r' r) eqn:Eq.
  - injection Hl as <-. left. unfold bv_eqb in Eq. apply Z.eqb_eq in Eq. apply bv_eq in Eq. subst. reflexivity.
  - right. exact (IH r e Hl).
Qed.

Lemma rt_get {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X R RT r e,
  regs_tblX w X R RT -> rt_lookup RT r = Some e -> PropExec.getr R r = edenot (Eseed bvmap_empty (wenv_vals w ++ X)) e.
Proof.
  intros w X R RT r e HT Hl. unfold regs_tblX in HT. rewrite Forall_forall in HT.
  exact (HT (r, e) (rt_lookup_in RT r e Hl)).
Qed.

Ltac rtf HT :=
  lazymatch goal with |- PropExec.getr ?R ?r = _ =>
    lazymatch type of HT with regs_tblX ?w ?X R ?RT =>
      let e := eval vm_compute in (rt_lookup RT r) in
      lazymatch e with Some ?ex =>
        rewrite (rt_get w X R RT r ex HT eq_refl);
        first [ reflexivity | eapply ev_add; [reflexivity | lia | lia] ]
      end
    end
  end.

Ltac pm_goX HHH LINVF OK X KR VIS RF HT Xs extra HKX fuel stops dirs nx ins' ks fks tbl' ftbl' RT' :=
  lazymatch type of X with PMXAT ?H ?LINV ?w ?s ?LB ?LBs ?m ?mo ?c ?ins ?tbl ?ftbl ?TB ?spal =>
  lazymatch type of HT with regs_tblX _ _ ?R ?RT =>
  lazymatch type of VIS with _ = MS _ ?F (Z_to_bv 64 ?pc) ?fc _ _ _ =>
    let kn0 := constr:(pm_kn_base tbl ftbl ++ extra) in
    let fixes := eval vm_compute in (skipn (length kn0) (kn_fix3 30 fuel ins stops (SCR dirs [] []) pc (srs sr_id RT) kn0 nx)) in
    let kn := constr:(pm_kn_base tbl ftbl ++ (extra ++ fixes)) in
    let r := eval vm_compute in (sym_exec ASEGS fuel true stops (SCR dirs [] []) (SS pc (srs sr_id RT) [] kn nx) []) in
    lazymatch r with (?ss', ?scs, ?scr') =>
      let SSr := fresh "SSr" in pose (SSr := ss');
      eapply (pm_run H HHH LINV LINVF w s LB LBs m mo c ins tbl ftbl TB spal _ R F fc pc RT Xs kn fuel stops (SCR dirs [] []) nx SSr scs scr'
                ins' ks fks tbl' ftbl' RT' _ OK X KR VIS RF (regs_tbl_ext w _ Xs R RT HT ltac:(vm_compute; reflexivity)));
      [ vm_compute; reflexivity
      | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
      | unfold know_ok; apply Forall_app; split;
        [ eapply (pm_kn_base_ok H HHH LINV w s LB LBs m mo c ins tbl ftbl TB spal _ OK X (env_world_seed H w R Xs));
          vm_compute; reflexivity
        | apply Forall_app; split; [exact HKX | cbn [List.app]; pmk_list H HHH w OK X (env_world_seed H w R Xs)] ]
      | idtac
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | idtac ]
    end end end end.

Lemma bv_add1_lit : forall a, 0 <= a -> a + 1 < 2 ^ 64 -> (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
Proof.
  intros a H0 H1. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  replace (bv_unsigned (1 : bv 64)) with 1 by reflexivity. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma rdn_ro_eq : forall m n a, mem_inv asegs m -> 0x10000 <= a -> a + Z.of_nat n <= 0x17e000 ->
  PropExec.rdn asegs m (Z_to_bv 64 a) n = PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros m n. induction n as [|n IH]; intros a MI H0 H1; [reflexivity|].
  cbn [PropExec.rdn].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb.
  { exfalso. pose proof (MI _ _ Eb) as R. rewrite (ro_addr_seg01 a ltac:(lia)) in R. discriminate. }
  rewrite (bv_add1_lit a) by lia. rewrite (IH (a + 1) MI) by lia. reflexivity.
Qed.

Lemma rdn_length : forall segs m n a bs, PropExec.rdn segs m a n = Some bs -> length bs = n.
Proof.
  intros segs m n. induction n as [|n IH]; intros a bs Hr; cbn [PropExec.rdn] in Hr.
  - injection Hr as <-. reflexivity.
  - destruct (match m a with Some b => Some b | None => PropExec.seg_rom segs a end) as [b|]; [|discriminate].
    destruct (PropExec.rdn segs m (a + 1)%bv n) as [r|] eqn:Er; [|discriminate].
    injection Hr as <-. cbn [length]. rewrite (IH _ _ Er). reflexivity.
Qed.

Lemma img_lit : forall m p n bs, mem_inv asegs m -> 0x10000 <= p -> p + Z.of_nat n <= 0x17e000 ->
  PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) n = Some bs ->
  bytes_at asegs m p bs /\ length bs = n.
Proof.
  intros m p n bs MI H0 H1 Hr. pose proof (rdn_length _ _ _ _ _ Hr) as L.
  split; [| exact L]. apply bytes_at_of_rdn; [lia | rewrite L; lia |].
  rewrite L, (rdn_ro_eq m n p MI H0 H1). exact Hr.
Qed.

Section Junk.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Lemma ff_u64_junk : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal k (j : nat),
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> AIMG_TOP <= wa_ff w -> 0 <= k -> k + 8 * Z.of_nat j <= 16384 ->
    exists ws, u64arr asegs m (wa_ff w + k) ws /\ length ws = j.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal k j X Hff Hk Hkj.
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (W0 & W1 & W2). change (fsz PM_FCLASS) with 16384 in *.
    assert (WR : wr_at asegs m (wa_ff w + k) (8 * Z.of_nat j)).
    { split; [lia|]. split; [lia|]. intros i Hi. replace (wa_ff w + k + i) with (wa_ff w + (k + i)) by lia. apply W2. lia. }
    destruct (rw_cells_of_wr_hi m (wa_ff w + k) (8 * Z.of_nat j) WR ltac:(lia) ltac:(lia)) as (bs & RB).
    replace (Z.to_nat (8 * Z.of_nat j)) with (8 * j)%nat in RB by lia.
    exact (u64arr_of_junk m _ j bs RB).
  Qed.

  Lemma ff_junk : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal k n,
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> AIMG_TOP <= wa_ff w -> 0 <= k -> 0 <= n -> k + n <= 16384 ->
    exists bs, rw_cells asegs m (wa_ff w + k) [CB (Z.to_nat n) bs].
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal k n X Hff Hk Hn Hkn.
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (W0 & W1 & W2). change (fsz PM_FCLASS) with 16384 in *.
    assert (WR : wr_at asegs m (wa_ff w + k) n).
    { split; [lia|]. split; [lia|]. intros i Hi. replace (wa_ff w + k + i) with (wa_ff w + (k + i)) by lia. apply W2. lia. }
    exact (rw_cells_of_wr_hi m (wa_ff w + k) n WR ltac:(lia) Hn).
  Qed.
End Junk.

Lemma sc_rd_fld8 : forall E m (sa : saddr) a v e,
  fld ASEGS m a 8 v -> adenot E sa = Z_to_bv 64 a -> edenot E e = Z_to_bv 64 v ->
  sc_denot asegs m E (SCReadBase sa 8 false e).
Proof.
  intros E m sa a v e HF Ha He. cbn [sc_denot]. exists (word_to_le_bytes 8 (Z_to_bv 64 v)). rewrite Ha. split; [exact HF|].
  unfold extz. rewrite SeqExec.bytes_le_to_Z_8, Z_to_bv_bv_unsigned. symmetry. exact He.
Qed.
