(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfPcE.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* printf_core (fm.asan 0x8f278), second pass: the walk state at the entry, from apcore's premises. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfPc0 FMsnprintfPcA FMsnprintfPcV FMsnprintfPcW.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Set Default Proof Using "All".
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis AFWX : afwx_realizesU B A_FWX.
Hypothesis ASNL : astrnlen_realizesU B W_STRNLEN.
Hypothesis ASNLN : astrnlenN_realizesU B W_STRNLEN.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (sp0 D N M P : Z) (nsl : nat).
Hypothesis HB : snk_base B ly S U W mem0 md0 sp0.
Hypothesis HD : snk_dest B ly S W mem0 D M.
Hypothesis HMN : M <= N.
Hypothesis HRV : rom_viewN tfibsegs B W mem0.
Hypothesis HR : snk_regs B regs0 (sp0 + OSP_PC).
Hypothesis HP1 : sp0 + 0x200 <= P.
Hypothesis HP2 : P + 8 * Z.of_nat nsl <= ly_stk_hi ly.
Hypothesis G10 : getr regs0 10 = w64 (sp0 + FO).
Hypothesis G12 : getr regs0 12 = w64 (sp0 + OSP_PC).
Hypothesis G13 : getr regs0 13 = w64 (sp0 + OSP_PC + 0x60).
Hypothesis G14 : getr regs0 14 = w64 (sp0 + OSP_PC + 0x108).
Hypothesis HAP : val_mem tfibsegs (mrestrict (w_H W) mem0) (sp0 + OSP_PC) 8 P.
Hypothesis HSNK : SNK W mem0 sp0 D N [] 0.
Hypothesis HMr : 1 <= M.
Lemma hbf : alloc_ceiling <= ly_stk_lo ly /\ 2 ^ 44 <= sp0 /\ sp0 mod 16 = 0 /\ ly_stk_lo ly + SNK_STK <= sp0 /\
  sp0 + 0x200 <= ly_stk_hi ly /\ sp0 + 0x200 <= 2 ^ 47 /\ kHighMemBeg <= sp0 - SNK_STK /\ ly_stk_hi ly <= 2 ^ 47.
Proof. exact (hb_facts B LAWS TB AFWX ASNL ASNLN ly S U W regs0 mem0 md0 sp0 D N M P nsl HB HD HMN HRV HR HP1 HP2). Qed.
Definition Ex (fv cval : Z) (vs : list Z) : env := kenv regs0 sp0 (Z_to_bv 64 P :: Z_to_bv 64 cval :: map (Z_to_bv 64) vs).
Lemma Ex_2 : forall fv cval vs, bv_unsigned (ew (Ex fv cval vs) 2) = sp0.
Proof. intros. unfold Ex. rewrite kenv_2. apply unsigned_lit_small. pose proof hbf. lia. Qed.
Lemma Ex_reg : forall fv cval vs i (r : bv 5), i <> 2%nat -> Z.of_nat i = bv_unsigned r -> ew (Ex fv cval vs) i = getr regs0 r.
Proof. intros. unfold Ex. apply kenv_reg; assumption. Qed.
Lemma Ex_x : forall fv cval vs j, ew (Ex fv cval vs) (32 + j) = nth j (Z_to_bv 64 P :: Z_to_bv 64 cval :: map (Z_to_bv 64) vs) (Z_to_bv 64 0).
Proof. intros. unfold Ex. apply kenv_x. Qed.
Lemma Ex_regs_ok : forall fv cval vs, getr regs0 11 = w64 fv -> regs_ok (Ex fv cval vs) (pc_regs 1 fv) regs0.
Proof.
intros fv cval vs G11. pose proof (Ex_2 fv cval vs) as E2. pose proof HR as (_ & R2 & _).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
  match goal with |- getr _ ?r = sv_denot _ (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first [ reflexivity
        | (rewrite Z.add_0_r;
           match goal with |- getr _ ?r = Z_to_bv 64 (bv_unsigned (ew _ ?i)) =>
             rewrite (Ex_reg fv cval vs i r) by (cbv; first [discriminate | reflexivity]) end;
           rewrite Z_to_bv_bv_unsigned; reflexivity)
        | (rewrite E2; first [rewrite R2 | rewrite G10 | rewrite G12 | rewrite G13 | rewrite G14]; unfold w64; f_equal;
           unfold FO, OSP_PC; lia)
        | (rewrite G11; reflexivity) ] |]).
destruct Hr.
Qed.
(* the regions after the stack *)
Lemma gotc_ok : forall E, region_ok tfibsegs E (mrestrict (w_H W) mem0) pc_gotc.
Proof.
intros E. pose proof HB as (HA & _).
pose proof (got_canary_of_AR B TB ly S W (unpoison U mem0) md0 (ARU_AR tfibsegs B ly S U W mem0 md0 HA)) as Hg.
assert (Hgot : val_mem tfibsegs (mrestrict (w_H W) mem0) FM_GOT_canary 8 FM_canary).
{ intros k Hk.
  transitivity (mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem0)) (A_GOT_CANARY + Z.of_nat k)); [|exact (Hg k Hk)].
  change A_GOT_CANARY with FM_GOT_canary. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly S U W mem0 md0 (Z_to_bv 64 (FM_GOT_canary + Z.of_nat k)) HA); [reflexivity|].
  rewrite unsigned_lit_small by (unfold FM_GOT_canary; lia). unfold FM_GOT_canary, SHADOW_OFF. lia. }
unfold region_ok, pc_gotc. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold FM_GOT_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | unfold FM_canary; zside | zside |].
rewrite Z.add_0_l. exact Hgot.
Qed.
(* the extra atoms: 32 = P, 33 = the guard's value, 34 + j = the j-th slot value *)
Lemma Ex_32 : forall fv cval vs, bv_unsigned (ew (Ex fv cval vs) 32) = P.
Proof.
intros. change 32%nat with (32 + 0)%nat. rewrite Ex_x. cbn [nth]. apply unsigned_lit_small.
pose proof hbf as (_ & H44 & _ & _ & _ & _ & _ & H47). pose proof HP2. lia.
Qed.
Lemma Ex_33 : forall fv cval vs, ew (Ex fv cval vs) 33 = Z_to_bv 64 cval.
Proof. intros. change 33%nat with (32 + 1)%nat. rewrite Ex_x. reflexivity. Qed.
Lemma Ex_slot : forall fv cval vs j, ew (Ex fv cval vs) (34 + j) = Z_to_bv 64 (nth j vs 0).
Proof.
intros. change (34 + j)%nat with (32 + (2 + j))%nat. rewrite Ex_x. cbn [nth Nat.add].
exact (map_nth (Z_to_bv 64) vs 0 j).
Qed.
Lemma Ex_slotu : forall fv cval vs j v, nth j vs 0 = v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ex fv cval vs) (34 + j)) = v.
Proof. intros fv cval vs j v Hn Hv. rewrite Ex_slot, Hn. apply unsigned_lit_small. exact Hv. Qed.
Lemma slot_chunk : forall fv cval vs j v, nth j vs 0 = v -> 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) (P + 8 * Z.of_nat j) 8 v ->
  YP09.chunk_ok tfibsegs (Ex fv cval vs) (mrestrict (w_H W) mem0) P
    (YP09.mkChunk (8 * Z.of_nat j) (CVal 8 (SOff (34 + j) 0))).
Proof.
intros fv cval vs j v Hn Hv Hm. apply (chunk_ok_val tfibsegs _ _ P _ 8 _ v); [| zside | zside | exact Hm].
cbn [sv_denot]. rewrite (Ex_slotu fv cval vs j v Hn Hv), Z.add_0_r. reflexivity.
Qed.
(* the entry state for any slot count: the slot region, regions_wf, the facts and the pinned atoms handed in *)
Lemma entry_gen : forall fv cval vs n A, getr regs0 11 = w64 fv ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) FM_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
  regions_wf (pc_stk :: pc_rest n ++ [pc_gotc]) = true ->
  region_ok tfibsegs (Ex fv cval vs) (mrestrict (w_H W) mem0) (pc_slots n) -> P + 8 * Z.of_nat n <= ly_stk_hi ly ->
  facts_ok (Ex fv cval vs) (if (n =? 1)%nat then pc_facts_s else pc_facts_p) ->
  Forall (fun p => bv_unsigned (ew (Ex fv cval vs) (fst p)) = snd p) A ->
  WS B ly S U W regs0 mem0 md0 sp0 D N M P A [] (Ex fv cval vs) (pc_s0 fv n)
    (mkst regs0 (Z_to_bv 64 A_PCORE) mem0 (seg_rom tfibsegs)) md0.
Proof.
intros fv cval vs n A G11 Hcan Hcv Hwf Hsl Hn Hf HA.
pose proof hbf as (Hac & Hsp44 & Hsp16 & Hstk & Htop & Hsp47 & Hhigh & Hhi47).
pose proof HB as (HAR & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof (Ex_2 fv cval vs) as E2. pose proof (Ex_32 fv cval vs) as E32.
unfold WS. split; [|split; [reflexivity|split; [|split]]].
- rewrite restrict_mkst_fx. unfold pc_s0. apply kentry.
  + exact (Ex_regs_ok fv cval vs G11).
  + exact Hwf.
  + unfold pc_rest. cbn [app]. repeat apply Forall_cons; try apply Forall_nil.
    * unfold region_ok, pc_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E2. split; [unfold SNK_STK; lia|]. split; [lia|]. split.
      -- intros o Ho. apply YE2y.apresent_writable. apply Hpres. unfold snk_band, SNK_STK, OSP_PC in *. lia.
      -- constructor; [|constructor]. apply (chunk_ok_val tfibsegs _ _ sp0 OSP_PC 8 (SOff 32 0) P); [| zside | zside | exact HAP].
         cbn [sv_denot]. rewrite E32, Z.add_0_r. reflexivity.
    * unfold region_ok, pc_flg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E2. pose proof HSNK as (S0 & _). unfold FO in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. apply (chunk_ok_val tfibsegs _ _ sp0 0x30 4 (SLit 0) 0); [reflexivity | zside | zside | exact S0].
    * unfold region_ok, pc_can. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold FM_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. eapply (chunk_ok_val tfibsegs _ _ 0 _ 8 _ cval); [| zside | zside | rewrite Z.add_0_l; exact Hcan].
      cbn [sv_denot]. rewrite Ex_33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * exact Hsl.
    * exact (pc_ro_ok B _ W mem0 TB HRV).
    * apply gotc_ok.
  + apply pairwise_disjoint_of_extents.
    unfold pc_rest, pc_stk, pc_flg, pc_can, pc_slots, pc_ro, img_ro_region, pc_gotc, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E32.
    unfold SNK_STK, FO, FM_GOT_canary, FM_canary, IMG_RO_LO, IMG_RO_HI.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + exact Hf.
- cbn [ms_mem mkst]. unfold PI. split; [|split; [exists 0; exact HSNK | cbn [length Z.of_nat]; lia]].
  split; [exact HAR|]. split; [apply same_but_materialized_refl|]. split; [exact Hpres|].
  split; [intros; reflexivity | intros a Ha; exact Ha].
- unfold EF. split; [exact E2|]. split; [exact E32|]. intros i r _ Hi Hr. apply Ex_reg; assumption.
- exact HA.
Qed.
Lemma entry1 : forall fv p cval, getr regs0 11 = w64 fv ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) FM_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) P 8 p -> 4096 <= p < 2 ^ 47 -> P + 8 <= ly_stk_hi ly ->
  WS B ly S U W regs0 mem0 md0 sp0 D N M P [(34%nat, p)] [] (Ex fv cval [p]) (pc_s0 fv 1)
    (mkst regs0 (Z_to_bv 64 A_PCORE) mem0 (seg_rom tfibsegs)) md0.
Proof.
intros fv p cval G11 Hcan Hcv Hp Hpr Hph.
pose proof hbf as (Hac & Hsp44 & Hsp16 & Hstk & Htop & Hsp47 & Hhigh & Hhi47).
assert (E34 : bv_unsigned (ew (Ex fv cval [p]) 34) = p) by exact (Ex_slotu fv cval [p] 0 p eq_refl ltac:(lia)).
apply entry_gen; [exact G11 | exact Hcan | exact Hcv | vm_compute; reflexivity | | cbn [Z.of_nat]; lia | |].
- unfold region_ok, pc_slots.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val slot_chunks].
  rewrite Ex_32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor]. apply (slot_chunk fv cval [p] 0 p eq_refl); [lia|].
  replace (P + 8 * Z.of_nat 0) with P by lia. exact Hp.
- cbn [Nat.eqb]. unfold pc_facts_s. split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ex_2, Ex_32, E34.
  change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; lia.
- constructor; [exact E34 | constructor].
Qed.
Lemma entry3 : forall fv k p1 p2 cval, getr regs0 11 = w64 fv ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) FM_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) P 8 k -> val_mem tfibsegs (mrestrict (w_H W) mem0) (P + 8) 8 p1 ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) (P + 16) 8 p2 ->
  1 <= k <= 2 ^ 30 -> 4096 <= p1 < 2 ^ 47 -> 4096 <= p2 < 2 ^ 47 -> P + 24 <= ly_stk_hi ly ->
  WS B ly S U W regs0 mem0 md0 sp0 D N M P [(34%nat, k); (35%nat, p1); (36%nat, p2)] [] (Ex fv cval [k; p1; p2]) (pc_s0 fv 3)
    (mkst regs0 (Z_to_bv 64 A_PCORE) mem0 (seg_rom tfibsegs)) md0.
Proof.
intros fv k p1 p2 cval G11 Hcan Hcv Hk Hp1 Hp2 Hkr Hp1r Hp2r Hph.
pose proof hbf as (Hac & Hsp44 & Hsp16 & Hstk & Htop & Hsp47 & Hhigh & Hhi47).
assert (E34 : bv_unsigned (ew (Ex fv cval [k; p1; p2]) 34) = k)
  by exact (Ex_slotu fv cval [k; p1; p2] 0 k eq_refl ltac:(lia)).
assert (E35 : bv_unsigned (ew (Ex fv cval [k; p1; p2]) 35) = p1)
  by exact (Ex_slotu fv cval [k; p1; p2] 1 p1 eq_refl ltac:(lia)).
assert (E36 : bv_unsigned (ew (Ex fv cval [k; p1; p2]) 36) = p2)
  by exact (Ex_slotu fv cval [k; p1; p2] 2 p2 eq_refl ltac:(lia)).
apply entry_gen; [exact G11 | exact Hcan | exact Hcv | vm_compute; reflexivity | | cbn [Z.of_nat]; lia | |].
- unfold region_ok, pc_slots.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val slot_chunks].
  rewrite Ex_32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (slot_chunk fv cval [k; p1; p2] 0 k eq_refl); [lia|].
    replace (P + 8 * Z.of_nat 0) with P by lia. exact Hk.
  + apply (slot_chunk fv cval [k; p1; p2] 1 p1 eq_refl); [lia|].
    replace (P + 8 * Z.of_nat 1) with (P + 8) by lia. exact Hp1.
  + apply (slot_chunk fv cval [k; p1; p2] 2 p2 eq_refl); [lia|].
    replace (P + 8 * Z.of_nat 2) with (P + 16) by lia. exact Hp2.
- cbn [Nat.eqb]. unfold pc_facts_p. split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ex_2, Ex_32, E34, E35, E36.
  change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; lia.
- constructor; [exact E34 | constructor; [exact E35 | constructor; [exact E36 | constructor]]].
Qed.
End e.
