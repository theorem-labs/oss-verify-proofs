(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlkU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6b890_6badc.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6b914 : bv 32 := 0xa0e69653.

Definition W_6b918 : bv 32 := 0x00060863.

Definition W_6b91c : bv 32 := 0xc007b653.

Definition W_6b920 : bv 32 := 0xd0063753.

Definition W_6b924 : bv 32 := 0x20f707d3.

Definition W_6b928 : bv 32 := 0xbf800637.

Definition W_6b95c : bv 32 := 0x5556869b.

Definition W_6b960 : bv 32 := 0x3337071b.

Definition W_6b964 : bv 32 := 0xf0f7879b.

Definition W_6b968 : bv 32 := 0x1018081b.

Definition W_6b96c : bv 32 := 0x02069893.

Definition W_6b970 : bv 32 := 0x011686b3.

Definition W_6b974 : bv 32 := 0x02071893.

Definition W_6b978 : bv 32 := 0x01170733.

Definition W_6b97c : bv 32 := 0x02079893.

Definition W_6b980 : bv 32 := 0x011787b3.

Definition W_6b984 : bv 32 := 0x02081893.

Definition W_6b988 : bv 32 := 0x01180833.

Definition W_6b98c : bv 32 := 0x00145893.

Definition W_6b990 : bv 32 := 0x00d8f6b3.

Definition W_6b994 : bv 32 := 0x40d406b3.

Definition W_6b998 : bv 32 := 0x0026d893.

Definition W_6b99c : bv 32 := 0x00e6f6b3.

Definition W_6b9a0 : bv 32 := 0x00e8f733.

Definition W_6b9a4 : bv 32 := 0x00e686b3.

Definition W_6b9a8 : bv 32 := 0x0046d713.

Definition W_6b9ac : bv 32 := 0x00e686b3.

Definition W_6b9b0 : bv 32 := 0x00f6f6b3.

Definition W_6b9b4 : bv 32 := 0x030686b3.

Definition W_6b9b8 : bv 32 := 0x0386d693.

Definition W_6b9bc : bv 32 := 0x00100713.

Definition W_6b9c0 : bv 32 := 0x0cd76863.

Definition W_6b9c4 : bv 32 := 0x10060a63.

Definition W_6b9c8 : bv 32 := 0xc0379653.

Definition W_6b9cc : bv 32 := 0x00200693.

Definition W_6b9d0 : bv 32 := 0x0ed66263.

Definition W_6b9d4 : bv 32 := 0xfff60613.

Definition W_6b9dc : bv 32 := 0x33333737.

Definition W_6b9e0 : bv 32 := 0x0f0f17b7.

Definition W_6b9e4 : bv 32 := 0x00165813.

Definition W_6b9e8 : bv 32 := 0x5556869b.

Definition W_6b9fc : bv 32 := 0x010686b3.

Definition W_6ba00 : bv 32 := 0x02071813.

Definition W_6ba04 : bv 32 := 0x01070733.

Definition W_6ba08 : bv 32 := 0x02079813.

Definition W_6ba0c : bv 32 := 0x010787b3.

Definition W_6ba10 : bv 32 := 0x00265813.

Definition W_6ba14 : bv 32 := 0x01066633.

Definition W_6ba18 : bv 32 := 0x00465813.

Definition W_6ba1c : bv 32 := 0x01066633.

Definition W_6ba20 : bv 32 := 0x00865813.

Definition W_6ba24 : bv 32 := 0x01066633.

Definition W_6ba28 : bv 32 := 0x01065813.

Definition W_6ba2c : bv 32 := 0x01066633.

Definition W_6ba30 : bv 32 := 0x02065813.

Definition W_6ba34 : bv 32 := 0x01066633.

Definition W_6ba38 : bv 32 := 0xfff64613.

Definition W_6ba3c : bv 32 := 0x00165813.

Definition W_6ba40 : bv 32 := 0x00d876b3.

Definition W_6ba44 : bv 32 := 0x40d60633.

Definition W_6ba48 : bv 32 := 0x00e676b3.

Definition W_6ba4c : bv 32 := 0x00265613.

Definition W_6ba50 : bv 32 := 0x00e67633.

Definition W_6ba54 : bv 32 := 0x01010737.

Definition W_6ba58 : bv 32 := 0x1017071b.

Definition W_6ba5c : bv 32 := 0x00c68633.

Definition W_6ba60 : bv 32 := 0x00465693.

Definition W_6ba64 : bv 32 := 0x00d60633.

Definition W_6ba68 : bv 32 := 0x02071693.

Definition W_6ba6c : bv 32 := 0x00f67633.

Definition W_6ba70 : bv 32 := 0x00d706b3.

Definition W_6ba74 : bv 32 := 0x02d60633.

Definition W_6ba78 : bv 32 := 0x03865613.

Definition W_6ba7c : bv 32 := 0x04060e63.

Definition W_6ba80 : bv 32 := 0x40c0063b.

Definition W_6ba84 : bv 32 := 0x00100693.

End U1_code_6b890_6badc.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibBudget FPSteps SumMemsetLib SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HRepFacts HStmts HStmtsU1 HWord HConstsU1 HCommonU1 HBlkU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRehashW2U1.U1_code_6b890_6badc.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition RW       : Z := 0x6b8d0.
Definition NP_PC    : Z := 0x8c1fc.
Definition NPR      : Z := 0x6b90c.
Definition REH      : Z := 0x6bb1c.
Definition SHRINK   : Z := 0x6b934.

Definition STOPS : list Z := [NP_PC; NPR; REH; SHRINK].

Section RW.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Variables NEW_STACK DEL_STACK : Z.
  Hypothesis NEW_STACK_nn : 0 <= NEW_STACK.
  Hypothesis DEL_STACK_nn : 0 <= DEL_STACK.
  Hypothesis NP : next_prime_stmt SEGS L hc.
  Hypothesis REHASH : rehash24_stmt SEGS L MI ST NEW_STACK DEL_STACK REH.

  Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
  Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
  Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI HLimg_lo HLerr_rw).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw).

  Lemma hi_unowned : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
  Proof using AC L MI HLimg_lo HLrw_img.
    intros A M model a AI Ha Ho.
    destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw | Hni].
    - pose proof (HLimg_lo _ (HLrw_img _ Hrw)). lia.
    - pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hni). lia.
  Qed.

  Section Main.
    Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
    Variables (sp ret obj bl bc : Z) (ents : list (Z * (Z * Z))) (K : TSet).
    #[local] Notation n := (bseq_next bc).
    Hypothesis CB : callB MI ST A0 s R0 M0 model0 sp ret (REHASH_STACK NEW_STACK DEL_STACK).
    Hypothesis H10 : getr R0 10%bv = Z_to_bv 64 obj.
    Hypothesis H11 : getr R0 11%bv = Z_to_bv 64 (rw_arg bc).
    Hypothesis U0 : umapx MI 24 (nval24 SEGS) A0 M0 obj bl bc ents.
    Hypothesis Hlast : bc <> BSEQ_LAST.
    Hypothesis HNMAX : LIB_NMAX <= NMAX MI.
    Hypothesis ASP : above_sp MI A0 sp obj 40.
    Hypothesis RC0 : ro_clear L M0.
    Hypothesis ROOM : roomL MI A0 (live MI A0) (8 * n).
    Hypothesis CONT : forall A' R' M' model' (bl' : Z) (ents' : list (Z * (Z * Z))),
        retB MI ST A' s R0 R' M' model0 model' ->
        umapx MI 24 (nval24 SEGS) A' M' obj bl' n ents' ->
        Permutation ents' ents ->
        lapply (live MI A0) (LAdd bl' (8 * n) :: (if bc =? 0 then [] else [LDel bl])) (live MI A') ->
        eff MI A0 A' M0 M' (sp - REHASH_STACK NEW_STACK DEL_STACK, sp)
            (fun a => umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' n ents' a) ->
        srealizes SEGS (cfg fx R' ret M' model') K.

    Definition SS : Z := 48 + Z.max NEW_STACK DEL_STACK.
    Definition W : Z * Z := (sp - SS, sp).

    Let AI0 := cb_ainv _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let MS0 := cb_mstd _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let CR0 := cb_regs _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let ROC0 := cb_roc _ _ _ _ _ _ _ _ _ _ _ _ CB.

    Lemma sp_facts : sp mod 16 = 0 /\ alloc_ceiling + SS <= sp /\ sp < 2 ^ 47 /\ 0x124000 <= sp - SS /\ 48 <= SS.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret CB.
      destruct CR0. pose proof (cb_ceil _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hc. unfold REHASH_STACK in Hc. unfold SS.
      pose proof ac_bounds_lit. repeat split; try assumption; lia.
    Qed.

    Lemma n_facts : In n BSEQ /\ bc < n /\ 8 * n <= 2 ^ 28 /\ ((bc = 0 /\ n = 2) \/ (3 <= n /\ Z.land n (n - 1) <> 0)).
    Proof using AC L MI A0 M0 obj bl bc ents U0 Hlast. exact (bseq_next_facts bc (u_bseq U0) Hlast). Qed.
    #[local] Opaque bseq_next.

    Ltac zpc z := lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
                    replace pc with (Z_to_bv 64 z : word) by (apply bv_eq; vm_compute; reflexivity) end.

    Lemma tailcall : forall Rr Mr,
        ainv MI A0 Mr model0 ->
        (forall x : word, ~ (sp - 48 <= bv_unsigned x < sp) -> Mr x = M0 x) -> (forall x : word, M0 x <> None -> Mr x <> None) ->
        getr Rr 1%bv = Z_to_bv 64 ret -> getr Rr 2%bv = Z_to_bv 64 sp ->
        (forall r, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr Rr r = getr R0 r) ->
        getr Rr 10%bv = Z_to_bv 64 obj -> getr Rr 11%bv = Z_to_bv 64 n ->
        srealizes SEGS (cfg fx Rr REH Mr model0) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn REHASH HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc ents K CB U0 Hlast HNMAX ASP ROOM CONT.
      intros Rr Mr AIr HMw HMg G1 G2 Gs G10 G11.
      destruct sp_facts as (Hsp16 & Hsplo & Hsphi & Hspimg & Hss). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      pose proof (cb_room _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hroom. unfold REHASH_STACK in Hroom. fold SS in Hroom.
      pose proof (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hwin0. unfold REHASH_STACK in Hwin0. fold SS in Hwin0.
      pose proof (defined_of_stack_room M0 sp SS ltac:(lia) ltac:(unfold SS; lia) ltac:(lia) Hroom) as Hdef0.
      assert (EFc : eff MI A0 A0 M0 Mr W (fun _ => False)).
      { apply eff_store; [|exact HMg]. intros x HF HW. pose proof (u64_range x). apply HMw; intros Hx. apply HW. unfold W, W_of, SS. cbn. lia. }
      assert (ROCc : img_ro_clear L Mr).
      { eapply (img_ro_clear_via_eff' A0 A0 M0 Mr model0 W _ ROC0 AI0 EFc); [intros a [] | unfold W; cbn; lia]. }
      assert (SXc : sx_inv ST s Mr).
      { eapply (sx_inv_via_eff' s A0 A0 M0 Mr model0 W _ (cb_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) AI0 EFc
                 (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB)); [intros a [] | unfold W; cbn; lia]. }
      eapply (REHASH fx A0 s Rr Mr model0 sp ret obj bl bc ents K).
      - constructor; [exact AIr | exact MS0 | exact ROCc | exact SXc | exact (cb_sxh _ _ _ _ _ _ _ _ _ _ _ _ CB) | | exact (cb_ceil _ _ _ _ _ _ _ _ _ _ _ _ CB) | | exact (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) | exact (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) | exact (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB)].
        + constructor; [exact G1 | exact Hret | exact Hretr | exact G2 | exact Hsp16 | exact Hsphi | rewrite Gs by inl; exact Hgp | rewrite Gs by inl; exact Htp].
        + unfold REHASH_STACK. fold SS. apply stack_room_of_defined; [lia | lia | lia |]. intros i Hi; apply HMg; exact (Hdef0 i Hi).
      - exact G10.
      - exact G11.
      - destruct ASP as (Hs1 & Hh1 & Ho1).
        eapply (umapx_via_eff L MI HLimg_lo HLrw_img HLerr_rw 24 _ (nval24 SEGS) ltac:(lia) (nval24_agree SEGS) A0 A0 M0 Mr model0 obj bl bc ents W _ sp U0 AI0 EFc);
          [exact Hs1 | unfold W; cbn; lia | lia | intros i Hi; eapply hi_unowned; [exact AI0 | lia] | intros a _ [] | unfold W, SS in *; cbn; lia | intros q m Hb Hl; exact Hl].
      - exact Hlast.
      - exact HNMAX.
      - exact ASP.
      - exact ROOM.
      - intros A' R' M' model' bl' ents' RB U' PERM LAP EFF.
        destruct RB as [AI' MS' Hfs Hfds SX' KEPT].
        apply (CONT A' R' M' model' bl' ents'); [| exact U' | exact PERM | exact LAP |].
        + constructor; try assumption.
          intros r Hr. rewrite (KEPT r Hr). unfold callee_saved in Hr. cbn in Hr.
          repeat (destruct Hr as [<-|Hr]); try contradiction;
            first [ rewrite G1; symmetry; exact Hra | rewrite G2; symmetry; exact Hsp2 | apply Gs; inl ].
        + unfold REHASH_STACK in EFF |- *. fold SS in EFF |- *. change (sp - SS, sp) with W in EFF |- *.
          eapply eff_weaken; [eapply eff_trans; [exact EFc | exact EFF |]|].
          * intros a Ha. eapply hi_unowned; [exact AI' | unfold W, W_of in Ha; cbn in Ha; lia].
          * intros a [[]|Ha]. exact Ha.
    Qed.

    Theorem rehashw_correct : srealizes SEGS (cfg fx R0 RW M0 model0) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn NP REHASH HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc ents K CB H10 H11 U0 Hlast HNMAX ASP RC0 ROOM CONT.
      destruct sp_facts as (Hsp16 & Hsplo & Hsphi & Hspimg & Hss). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      destruct ASP as (Hs1 & Hh1 & Ho1).
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      pose proof (cb_room _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hroom. unfold REHASH_STACK in Hroom. fold SS in Hroom.
      pose proof (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hwin0. unfold REHASH_STACK in Hwin0. fold SS in Hwin0.
      pose proof (defined_of_stack_room M0 sp SS ltac:(lia) ltac:(unfold SS; lia) ltac:(lia) Hroom) as Hdef0.
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq U0) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
      pose proof (h_bc (u_hdr U0)) as Cbc. unfold cell8 in Cbc.
      pose proof (u64_range (getr R0 8)) as Hr8. pose proof (u64_range (getr R0 9)) as Hr9. pose proof (u64_range (getr R0 18)) as Hr18.
      pose (E := Eseed R0 [Z_to_bv 64 obj; Z_to_bv 64 (rw_arg bc); Z_to_bv 64 sp; getr R0 1%bv; getr R0 8%bv; getr R0 9%bv; getr R0 18%bv; Z_to_bv 64 bc]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34);
                                          (1%bv, EVar 35); (8%bv, EVar 36); (9%bv, EVar 37); (18%bv, EVar 38)]) R0).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; first [assumption | reflexivity]. }
      assert (HK : know_ok SEGS E M0 [KWr (SA (EVar 34) (-32)) (ELit 32); KDisj (SA (EVar 32) 0) (ELit 40) (SA (EVar 34) (-48)) (ELit 48)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - eapply (kwr_stack_sub _ _ _ _ sp SS); [evs; reflexivity | reflexivity | lia | lia | lia | exact Hroom].
        - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia]. }

      assert (FRM : forall Mc, (forall x : word, ~ (sp - 48 <= bv_unsigned x < sp) -> Mc x = M0 x) -> (forall x : word, M0 x <> None -> Mc x <> None) ->
                    ainv MI A0 Mc model0).
      { intros Mc HMcw HMcg. eapply (ai_frame MI); [exact AI0 | | exact HMcg | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply HMcw; intros Hx. exact (hi_unowned A0 M0 model0 (bv_unsigned x) AI0 ltac:(lia) Ho). }
      destruct (Z.eq_dec bc 0) as [Hbc | Hbc].
      -
        assert (Hn2 : n = 2) by (rewrite Hbc; reflexivity). clear Hncase.
        assert (Harg : rw_arg bc = 1) by (unfold rw_arg; rewrite Hbc; reflexivity).
        xruns HR HK 100%nat STOPS (SCR [false; false] [EVar 39] []) 50%N.
        { split_scs; try sc_auto1;
          first [ cbn [sc_denot]; evs; rewrite ?Harg, ?Hbc, ?Hn2; rewrite ?br_ne, ?br_geu by lia; bool_lia
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity] ]. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => rename H into HRc; rename Rx into Rc; set (Mc := Mx) end.
        assert (HMcw : forall x : word, ~ (sp - 48 <= bv_unsigned x < sp) -> Mc x = M0 x).
        { intros x Hx. pose proof (u64_range x). unfold Mc.
          rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMcg : forall x : word, M0 x <> None -> Mc x <> None) by (intros x Hx; unfold Mc; repeat apply wbytes_grows; exact Hx).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 9%bv G9. rreg HRc 18%bv G18. rreg HRc 10%bv G10. rreg HRc 11%bv G11.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
        apply (tailcall Rc Mc (FRM Mc HMcw HMcg) HMcw HMcg).
        + rewrite G1. exact Hra.
        + rewrite G2. nadd. rewrite ?v_addi_Z by lia. first [reflexivity | f_equal; lia].
        + intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]); try contradiction; first [exact G8 | exact G9 | exact G18 | apply Gs; inl].
        + exact G10.
        + rewrite G11. rewrite Hn2. reflexivity.
      -
        destruct Hncase as [[? _] | [Hn3 Hland]]; [lia|].
        assert (Harg : rw_arg bc = 2 * bc + 1) by (unfold rw_arg, np_arg; destruct (Z.eqb_spec bc 0); [lia | reflexivity]).
        pose proof (nparg_not_pow2 bc (u_bseq U0) Hbc) as Hnp2.
        assert (Hl2 : 0 <= Z.land (2 * bc + 1) (2 * bc + 1 - 1) <= 2 * (2 * bc + 1)).
        { pose proof (Z.add_lor_land (2 * bc + 1) (2 * bc + 1 - 1)). pose proof (Z.land_nonneg (2 * bc + 1) (2 * bc + 1 - 1)). pose proof (Z.lor_nonneg (2 * bc + 1) (2 * bc + 1 - 1)). lia. }
        pose proof (u_bseq U0) as HbB. unfold BSEQ in HbB. cbn in HbB.
        assert (Hbc28 : bc < 2 ^ 25) by lia. clear HbB.
        xruns HR HK 100%nat STOPS (SCR [true; false] [] []) 50%N.
        { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite Harg; nadd; repeat match goal with |- context [?x + -1] => change (x + -1) with (x - 1) end;
          rewrite ?w_and by lia; rewrite ?br_eq, ?br_ne by lia; bool_lia. }
        postrun.
        rewrite <- (Z_to_bv_bv_unsigned 64 (getr R0 8)), <- (Z_to_bv_bv_unsigned 64 (getr R0 9)), <- (Z_to_bv_bv_unsigned 64 (getr R0 18)). rewrite Hra.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => rename H into HRc; rename Rx into Rc; set (Mc := Mx) end.
        assert (HMcw : forall x : word, ~ (sp - 32 <= bv_unsigned x < sp) -> Mc x = M0 x).
        { intros x Hx. pose proof (u64_range x). unfold Mc.
          rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMcg : forall x : word, M0 x <> None -> Mc x <> None) by (intros x Hx; unfold Mc; repeat apply wbytes_grows; exact Hx).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 9%bv G9. rreg HRc 18%bv G18. rreg HRc 10%bv G10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.

        assert (F1 : cell8 SEGS Mc (sp - 8) ret) by (unfold Mc, cell8; cellpeel).
        assert (F2 : cell8 SEGS Mc (sp - 16) (bv_unsigned (getr R0 8%bv))) by (unfold Mc, cell8; cellpeel).
        assert (F3 : cell8 SEGS Mc (sp - 24) (bv_unsigned (getr R0 9%bv))) by (unfold Mc, cell8; cellpeel).
        assert (F4 : cell8 SEGS Mc (sp - 32) (bv_unsigned (getr R0 18%bv))) by (unfold Mc, cell8; cellpeel).
        assert (RCc : ro_clear L Mc).
        { intros w Hw. pose proof (u64_range w). rewrite HMcw; [exact (RC0 w Hw)|]. intros Hx. destruct Hw as (Himg & _). pose proof (HLimg_lo _ Himg). unfold SS in Hsplo. lia. }

        destruct (NP fx Rc Mc bc (sp - 32) (Z_to_bv 64 NPR) (u_bseq U0) Hbc Hlast ltac:(rewrite G10; rewrite Harg; reflexivity) G1
                     ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(rewrite G2; nadd; f_equal; lia)
                     ltac:(replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16) ltac:(lia) ltac:(lia)
                     ltac:(apply stack_room_of_defined; [lia | lia | lia |]; unfold Mc; repeat apply defined_wbytes; eapply defined_sub; [exact Hdef0 | unfold SS; lia | lia]) RCc)
          as (Rn & Hms & KEPT & Qa0).
        eapply srz_msteps; [eapply ms_halt; exact MS0 | eapply ms_lazy; exact MS0 | exact Hms |].
        replace (sp - 32 - 8) with (sp - 40) by lia. zpc NPR.
        set (Mn := wbytes Mc _ _).
        assert (HMnw : forall x : word, ~ (sp - 48 <= bv_unsigned x < sp) -> Mn x = M0 x).
        { intros x Hx. pose proof (u64_range x). unfold Mn. rewrite wbytes_outside; [apply HMcw; lia | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMng : forall x : word, M0 x <> None -> Mn x <> None) by (intros x Hx; unfold Mn; apply wbytes_grows; apply HMcg; exact Hx).
        assert (HMa : agree_on Mc Mn (sp - 32) 32).
        { intros i Hi. unfold Mn. pose proof (u64_range (Z_to_bv 64 (sp - 32 + i))). rewrite wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        Ltac frc F HMa := eapply cellw_agree; [exact F | eapply agree_on_sub; [exact HMa | lia | cbn; lia] | lia | cbn; lia].
        assert (F1' : cell8 SEGS Mn (sp - 8) ret) by frc F1 HMa.
        assert (F2' : cell8 SEGS Mn (sp - 16) (bv_unsigned (getr R0 8%bv))) by frc F2 HMa.
        assert (F3' : cell8 SEGS Mn (sp - 24) (bv_unsigned (getr R0 9%bv))) by frc F3 HMa.
        assert (F4' : cell8 SEGS Mn (sp - 32) (bv_unsigned (getr R0 18%bv))) by frc F4 HMa.
        unfold cell8 in F1', F2', F3', F4'.
        assert (Cbc' : cellw SEGS Mn (obj + 8) 8 bc).
        { eapply cellw_agree; [exact Cbc | | lia | cbn; lia]. intros i Hi. symmetry. first [apply HMnw | symmetry; apply HMnw]. rewrite u64_of_Z by lia. unfold SS in Hsplo. lia. }
        unfold ret_ok in Hret.
        pose (E2 := Eseed Rn [Z_to_bv 64 obj; Z_to_bv 64 n; Z_to_bv 64 (sp - 32); Z_to_bv 64 bc; Z_to_bv 64 ret; getr R0 8%bv; getr R0 9%bv; getr R0 18%bv]).
        assert (HR2 : regs_ok E2 (srs sr_id [(8%bv, EVar 32); (10%bv, EVar 33); (2%bv, EVar 34)]) Rn).
        { assert (G2' : getr Rc 2%bv = Z_to_bv 64 (sp - 32)) by (rewrite G2; nadd; rewrite ?v_addi_Z by lia; first [reflexivity | f_equal; lia]).
          apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
            first [exact Qa0 | rewrite (KEPT 8%bv ltac:(unfold callee_saved; inl)); exact G8 | rewrite (KEPT 2%bv ltac:(unfold callee_saved; inl)); exact G2']. }
        assert (HK2 : know_ok SEGS E2 Mn []) by constructor.
        xruns HR2 HK2 100%nat STOPS (SCR [false] [EVar 35; EVar 36; EVar 37; EVar 38; EVar 39] []) 50%N.
        { split_scs;
          first [ eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity]
                | cbn [sc_denot]; evs; rewrite br_geu by lia; bool_lia
                | eapply sc_flat; [evs; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F1'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity]
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F2'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity]
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F3'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity]
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F4'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity] ]. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
        rreg HRr 1%bv T1. rreg HRr 2%bv T2. rreg HRr 8%bv T8. rreg HRr 9%bv T9. rreg HRr 18%bv T18. rreg HRr 10%bv T10. rreg HRr 11%bv T11.
        rewrite ?Z_to_bv_bv_unsigned in T8, T9, T18.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Ts.
        apply (tailcall Rr Mn (FRM Mn HMnw HMng) HMnw HMng).
        + exact T1.
        + rewrite T2. nadd. rewrite ?v_addi_Z by lia. first [reflexivity | f_equal; lia].
        + intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]); try contradiction;
            first [exact T8 | exact T9 | exact T18 | rewrite Ts by inl; rewrite KEPT by (unfold callee_saved; inl); apply Gs; inl].
        + exact T10.
        + exact T11.
    Qed.
  End Main.

  Theorem rehashw_spec : rehashw_stmt SEGS L MI ST NEW_STACK DEL_STACK RW.
  Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn NP REHASH HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw.
    intros fx A s R M model sp ret obj bl bc ents K CB H10 H11 U0 Hlast HNMAX ASP RC ROOM CONT.
    eapply rehashw_correct; eassumption.
  Qed.
End RW.
