(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HUbsan OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlkU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRehashModel.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6badc_6bd00.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6bcf4 : bv 32 := 0x00008067.
Lemma F_6bcf4 : fetch_word Ubsan.M.loaded_segments (0x6bd34 : word) = Some W_6bcf4.
Proof. vm_refl. Qed.
Lemma D_6bcf4 : decode_any W_6bcf4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6badc_6bd00.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.U1_code_6f888_6f894.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibBudget FPSteps SumMemsetLib SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HRepFacts HStmts HWord HUbsan HConstsU1 HCommonU1 HBlkU1 HRehashModel.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRehash2U1B.U1_code_6badc_6bd00. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import U1_code_6f888_6f894.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition REH      : Z := 0x6bb1c.
Definition NEWE     : Z := 0xe7b34.
Definition NEWR     : Z := 0x6bb48.
Definition DRET     : Z := 0x6bb64.
Definition C_PC     : Z := 0x6bb64.
Definition ZL_PC    : Z := 0x6bb88.
Definition D_PC     : Z := 0x6bbac.
Definition LOOP_PC  : Z := 0x6bc80.
Definition EXIT_PC  : Z := 0x6bd24.
Definition RET_PC   : Z := 0x6bd34.
Definition TRAP_PC  : Z := 0x6bd3c.
Definition DELSZ    : Z := 0x6f8cc.
Definition DELETE   : Z := 0x6f8c8.

Definition STOPS : list Z := [NEWE; NEWR; DELSZ; C_PC; ZL_PC; D_PC; LOOP_PC; EXIT_PC; RET_PC; TRAP_PC].

Definition popcD : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec SEGS 100 true [0x6bc30; EXIT_PC; TRAP_PC] (SCR [false; false] [EVar 37; EVar 38] [])
                          (SS D_PC (srs sr_id [(10%bv, EVar 32); (9%bv, EVar 33); (2%bv, EVar 34); (8%bv, EVar 35); (15%bv, EVar 36)]) [] [] 50) [] in
     sr_get (s_regs ss) 12%bv).
Definition popcDw (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popcD.
Lemma popcD_env : forall E, edenot E popcD = popcDw (ev E 35).
Proof. intros E. unfold popcDw, popcD. cbn [edenot ev]. reflexivity. Qed.

Ltac vm_popcD :=
  match goal with |- context [bv_unsigned (popcDw ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcDw w)) in
    replace (bv_unsigned (popcDw w)) with v by (vm_compute; reflexivity) end.

Lemma popcD_ge2 : forall bc, In bc BSEQ -> bc <> 0 -> bc <> BSEQ_LAST ->
  2 <= bv_unsigned (popcDw (Z_to_bv 64 (bseq_next bc))).
Proof.
  intros bc Hin Hnz Hl. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; first [lia | apply Hl; reflexivity]
            | cbn [bseq_next BSEQ tl hd List.find]; vm_popcD; lia ] |]).
  destruct Hin.
Qed.

Section Reh.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Variables NEW_STACK DEL_STACK : Z.
  Hypothesis NEW_STACK_nn : 0 <= NEW_STACK.
  Hypothesis DEL_STACK_nn : 0 <= DEL_STACK.
  Hypothesis NEW : new_rule_stmt SEGS L MI ST NEW_STACK.
  Hypothesis DEL : delete_rule_stmt SEGS L MI DEL_STACK.

  Hypothesis HLnew : ly_new L = NEWE.
  Hypothesis HLdel : ly_delete L = DELETE.
  Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
  Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
  Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI HLimg_lo HLrw_img HLerr_rw).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI HLimg_lo HLerr_rw).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw).

  Lemma hi_unowned : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
  Proof using AC L MI HLimg_lo HLrw_img.
    intros A M model a AI Ha Ho.
    destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw | Hni].
    - pose proof (HLimg_lo _ (HLrw_img _ Hrw)). lia.
    - pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hni). lia.
  Qed.

  Lemma eff_widen : forall (A A' : AS MI) M M' (W W' : Z * Z) F,
    eff MI A A' M M' W F -> (forall a, W_of W a -> W_of W' a) -> eff MI A A' M M' W' F.
  Proof using AC L MI.
    intros A A' M M' W0 W' F E HW. destruct E as [C B O FR D OI]. constructor; try assumption.
    intros a Hn. apply FR. intros [H|[H|[H|[H|[H|H]]]]]; apply Hn; try tauto. right; right; right; right; left. apply HW, H.
  Qed.

  Lemma umap_foot_hb : forall {V : Type} NS obj bl bc (ents : list (Z * (Z * V))) a,
    umap_foot NS obj bl bc ents a -> (obj <= a < obj + 40) \/ exists b, In b (umap_blocks NS bl bc ents) /\ fst b <= a < fst b + snd b.
  Proof using.
    intros V NS obj bl bc ents a [Hh | [[Hbc Hb] | (p & Hp & Hpa)]]; [left; exact Hh | right | right].
    - exists (bl, 8 * bc). split; [| exact Hb]. unfold umap_blocks. destruct (Z.eqb_spec bc 0); [lia|]. apply in_app_iff. left. left. reflexivity.
    - apply in_map_iff in Hp. destruct Hp as ([p' kv] & Hpp & Hin). cbn in Hpp. subst p'.
      exists (p, NS). split; [| exact Hpa]. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (p, kv). split; [reflexivity | exact Hin].
  Qed.

  Lemma roomL_room_for : forall (A : AS MI) M model n,
    ainv MI A M model -> 0 <= n <= NMAX MI -> roomL MI A (live MI A) n -> room_for MI A n.
  Proof using AC L MI.
    intros A M model n AI Hn [HS HBG].
    destruct (Z.lt_ge_cases n (BIG MI)) as [Hs|Hb].
    - destruct (HS Hs) as [H1 H2]. eapply (room_small MI); [exact AI | lia | exact H1 | exact H2].
    - eapply (room_big MI); [exact AI | lia | apply HBG; lia].
  Qed.

  Lemma bseq_next_facts : forall bc, In bc BSEQ -> bc <> BSEQ_LAST ->
    In (bseq_next bc) BSEQ /\ bc < bseq_next bc /\ 8 * bseq_next bc <= 2 ^ 28
    /\ ((bc = 0 /\ bseq_next bc = 2) \/ (3 <= bseq_next bc /\ Z.land (bseq_next bc) (bseq_next bc - 1) <> 0)).
  Proof using.
    intros bc Hin Hlast. unfold BSEQ in Hin. unfold BSEQ_LAST in Hlast.
    repeat (destruct Hin as [<-|Hin];
      [ first [ exfalso; lia
              | match goal with |- context [bseq_next ?b] => let v := eval vm_compute in (bseq_next b) in change (bseq_next b) with v end;
                split; [inl | split; [lia | split; [lia | first [left; split; reflexivity | right; split; [lia | vm_compute; discriminate]]]]] ] |]).
    destruct Hin.
  Qed.

  Lemma del_call : forall fx A M model R (p n spc r : Z) K,
    ainv MI A M model -> mstd model -> img_ro_clear L M ->
    getr R 1%bv = Z_to_bv 64 r -> ret_ok (Z_to_bv 64 r) -> 0 <= r < 2 ^ 64 ->
    getr R 2%bv = Z_to_bv 64 spc -> spc mod 16 = 0 -> spc < 2 ^ 47 ->
    getr R 3%bv = Z_to_bv 64 (ly_gp L) -> getr R 4%bv = Z_to_bv 64 (ly_tp L) ->
    getr R 10%bv = Z_to_bv 64 p -> (p = 0 /\ n = 0 \/ In (p, n) (live MI A)) ->
    alloc_ceiling + DEL_STACK <= spc -> 0x124000 <= spc - DEL_STACK ->
    defined M (spc - DEL_STACK) DEL_STACK ->
    (forall a, zwin (spc - DEL_STACK) spc a -> ~ owned MI A a) ->
    (forall A' R' M' model',
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
        kept R R' -> live_del p (live MI A) (live MI A') ->
        eff MI A A' M M' (spc - DEL_STACK, spc) (fun a => p <= a < p + n) ->
        defined M' (spc - DEL_STACK) DEL_STACK ->
        (forall a, zwin (spc - DEL_STACK) spc a -> ~ owned MI A' a) ->
        srealizes SEGS (cfg fx R' r M' model') K) ->
    srealizes SEGS (cfg fx R DELSZ M model) K.
  Proof using AC L MI DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw.
    intros fx A M model R p n spc r K AI MS ROC H1 Hret Hr H2 Hsp16 Hsphi H3 H4 H10 Hp Hce Hlo Hdef Hwin POST.
    pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ].
    { unfold DELSZ. norm_pc. stepj F_6f88c D_6f88c. apply mst_refl. }
    replace (0x6f8c8%bv : word) with (Z_to_bv 64 (ly_delete L)) by (rewrite HLdel; apply bv_eq; reflexivity).
    eapply (DEL fx A R M model p n spc r K AI MS ROC).
    - constructor; assumption.
    - exact H10.
    - exact Hp.
    - lia.
    - apply stack_room_of_defined; [lia | lia | lia | exact Hdef].
    - exact Hwin.
    - intros A' R2 M' model' AI' MS' Hfs Hfds KEPT LDEL CAPS BIGC OWN FR DEF.
      assert (Hdef' : defined M' (spc - DEL_STACK) DEL_STACK).
      { intros i Hi. destruct (DEF (Z_to_bv 64 (spc - DEL_STACK + i)) (Hdef i Hi)) as [Hm|[Ho|[Hq|He]]];
          [exact Hm| exfalso | exfalso | exfalso].
        - rewrite u64_of_Z in Ho by lia. exact (Hwin (spc - DEL_STACK + i) ltac:(unfold zwin; lia) Ho).
        - rewrite u64_of_Z in Hq by lia. destruct Hp as [[-> ->]|Hin]; [lia|].
          destruct (live_facts' A M model p n AI Hin) as (_ & _ & Hpc & _). lia.
        - rewrite u64_of_Z in He by lia. pose proof (HLimg_lo _ (HLrw_img _ (HLerr_rw _ He))). lia. }
      assert (Hwin' : forall a, zwin (spc - DEL_STACK) spc a -> ~ owned MI A' a).
      { intros a Ha Ho. destruct (OWN a Ho) as [Ho0|Hq]; [exact (Hwin a Ha Ho0)|]. unfold zwin in Ha.
        destruct Hp as [[-> ->]|Hin]; [lia|]. destruct (live_facts' A M model p n AI Hin) as (_ & _ & Hpc & _). lia. }
      apply (POST A' R2 M' model' AI' MS' Hfs Hfds KEPT LDEL); [| exact Hdef' | exact Hwin'].
      eapply eff_of_del; [exact CAPS | exact BIGC | exact OWN | exact FR | exact DEF | | intros a Ha; exact Ha
                        | intros a Ha; destruct Hp as [[-> ->]|Hin]; [lia | exact (live_offimg' A M model p n a AI Hin Ha)]].
      intros a Ha. exact Ha.
  Qed.

  Section Main.
    Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
    Variables (sp ret obj bl bc : Z) (ents : list (Z * (Z * Z))) (K : TSet).
    #[local] Notation n := (bseq_next bc).
    Hypothesis CB : callB MI ST A0 s R0 M0 model0 sp ret (REHASH_STACK NEW_STACK DEL_STACK).
    Hypothesis H10 : getr R0 10%bv = Z_to_bv 64 obj.
    Hypothesis H11 : getr R0 11%bv = Z_to_bv 64 n.
    Hypothesis U0 : umapx MI 24 (nval24 SEGS) A0 M0 obj bl bc ents.
    Hypothesis Hlast : bc <> BSEQ_LAST.
    Hypothesis HNMAX : LIB_NMAX <= NMAX MI.
    Hypothesis ASP : above_sp MI A0 sp obj 40.
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

    Definition base_ok (R : bvmap 5 word) : Prop :=
      getr R 2%bv = Z_to_bv 64 (sp - 32) /\ getr R 3%bv = Z_to_bv 64 (ly_gp L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp L)
      /\ forall r, In r [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R r = getr R0 r.

    Definition frame (M : mem) : Prop :=
      cell8 SEGS M (sp - 8) ret /\ cell8 SEGS M (sp - 16) (bv_unsigned (getr R0 8%bv)) /\ cell8 SEGS M (sp - 24) (bv_unsigned (getr R0 9%bv)).

    Let AI0 := cb_ainv _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let MS0 := cb_mstd _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let CR0 := cb_regs _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let ROC0 := cb_roc _ _ _ _ _ _ _ _ _ _ _ _ CB.

    Lemma sp_facts : sp mod 16 = 0 /\ alloc_ceiling + SS <= sp /\ sp < 2 ^ 47 /\ 0x124000 <= sp - SS /\ 48 + NEW_STACK <= SS /\ 48 + DEL_STACK <= SS.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret CB.
      destruct CR0. pose proof (cb_ceil _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hc. unfold REHASH_STACK in Hc. unfold SS.
      pose proof ac_bounds_lit. repeat split; try assumption; lia.
    Qed.
    Let SPF := sp_facts.

    Lemma n_facts : In n BSEQ /\ bc < n /\ 8 * n <= 2 ^ 28 /\ ((bc = 0 /\ n = 2) \/ (3 <= n /\ Z.land n (n - 1) <> 0)).
    Proof using AC L MI A0 M0 obj bl bc ents U0 Hlast. exact (bseq_next_facts bc (u_bseq U0) Hlast). Qed.
    #[local] Opaque bseq_next.

    Lemma tbl_blocks_live : forall b, In b (umap_blocks 24 bl bc ents) -> In b (live MI A0).
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn fx A0 s R0 M0 model0 sp ret obj bl bc ents K CB U0 CONT.
      intros [p m] Hb. unfold umap_blocks in Hb. apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
      - destruct (Z.eqb_spec bc 0); [destruct Hb|]. destruct Hb as [Hb|[]]. injection Hb as <- <-.
        destruct (u_blive U0) as [[? ?]|[_ Hin]]; [lia | exact Hin].
      - apply in_map_iff in Hb. destruct Hb as ([p' [k v]] & Hpp & Hin). cbn in Hpp. injection Hpp as <- <-.
        exact (proj1 (u_node U0 p' k v Hin)).
    Qed.

    Lemma foot_offimg : forall a, umap_foot 24 obj bl bc ents a -> ~ in_ranges (ly_img L) a.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn HLimg_lo A0 s R0 M0 model0 sp ret obj bl bc ents CB U0 ASP.
      intros a Ha Himg. pose proof (HLimg_lo a Himg) as Hlt. destruct SPF as (_ & Hsplo & _). destruct ASP as (Hs & _).
      destruct Ha as [Hh | [[Hbc Hb] | (p & Hp & Hpa)]]; [unfold SS in Hsplo; lia | |].
      - destruct (u_blive U0) as [[? ?]|[_ Hin]]; [lia|]. exact (live_offimg' A0 M0 model0 bl (8 * bc) a AI0 Hin Hb Himg).
      - apply in_map_iff in Hp. destruct Hp as ([p' [k v]] & Hpp & Hin). cbn in Hpp. subst p'.
        exact (live_offimg' A0 M0 model0 p 24 a AI0 (proj1 (u_node U0 p k v Hin)) Hpa Himg).
    Qed.

    Ltac zpc z := lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
                    replace pc with (Z_to_bv 64 z : word) by (apply bv_eq; vm_compute; reflexivity) end.

    Lemma phaseA :
      (forall A1 M1 model1 R1 (p : Z),
          ainv MI A1 M1 model1 -> mstd model1 -> m_fs model1 = m_fs model0 -> m_fds model1 = m_fds model0 ->
          base_ok R1 -> getr R1 10%bv = Z_to_bv 64 p -> getr R1 8%bv = Z_to_bv 64 n -> getr R1 9%bv = Z_to_bv 64 obj ->
          frame M1 -> defined M1 (sp - SS) SS ->
          0 < p -> p + 8 * n <= alloc_ceiling -> p mod 16 = 0 -> live_add p (8 * n) (live MI A0) (live MI A1) ->
          eff MI A0 A1 M0 M1 W (fun a => p <= a < p + 8 * n) ->
          umapx MI 24 (nval24 SEGS) A1 M1 obj bl bc ents ->
          srealizes SEGS (cfg fx R1 NEWR M1 model1) K) ->
      srealizes SEGS (cfg fx R0 REH M0 model0) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn NEW HLnew HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc ents K CB H10 H11 U0 Hlast HNMAX ASP ROOM CONT.
      intros POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      destruct ASP as (Hs1 & Hh1 & Ho1).
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      pose proof (cb_room _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hroom. unfold REHASH_STACK in Hroom. fold SS in Hroom.
      pose proof (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hwin0. unfold REHASH_STACK in Hwin0. fold SS in Hwin0.
      pose proof (defined_of_stack_room M0 sp SS ltac:(lia) ltac:(unfold SS; lia) ltac:(lia) Hroom) as Hdef0.
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq U0) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose (E := Eseed R0 [Z_to_bv 64 obj; Z_to_bv 64 n; Z_to_bv 64 sp; getr R0 1%bv; getr R0 8%bv; getr R0 9%bv]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34);
                                          (1%bv, EVar 35); (8%bv, EVar 36); (9%bv, EVar 37)]) R0).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; first [assumption | reflexivity]. }
      assert (HK : know_ok SEGS E M0 [KWr (SA (EVar 34) (-32)) (ELit 32)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        eapply (kwr_stack_sub _ _ _ _ sp SS); [evs; reflexivity | reflexivity | lia | lia | lia | exact Hroom]. }
      xruns HR HK 100%nat STOPS (SCR [false; false] [] []) 50%N.
      { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_srl by lia. rewrite (Z.div_small n (2 ^ 61)) by lia. rewrite br_ne by lia. bool_lia. }
      postrun.
      rewrite <- (Z_to_bv_bv_unsigned 64 (getr R0 9)), <- (Z_to_bv_bv_unsigned 64 (getr R0 8)).
      rewrite Hra.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
      set (Mc := wbytes (wbytes (wbytes M0 _ _) _ _) _ _).
      rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 9%bv G9. rreg HRc 10%bv G10.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
      pose proof (u64_range (getr R0 8)) as Hr8. pose proof (u64_range (getr R0 9)) as Hr9.
      assert (HMcw : forall x : word, ~ (sp - 32 <= bv_unsigned x < sp) -> Mc x = M0 x).
      { intros x Hx. pose proof (u64_range x). unfold Mc.
        rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
      assert (HMcg : forall x : word, M0 x <> None -> Mc x <> None) by (intros x Hx; unfold Mc; repeat apply wbytes_grows; exact Hx).
      assert (AIc : ainv MI A0 Mc model0).
      { eapply (ai_frame MI); [exact AI0 | | exact HMcg | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply HMcw; intros Hx. exact (hi_unowned A0 M0 model0 (bv_unsigned x) AI0 ltac:(lia) Ho). }
      assert (EFc : eff MI A0 A0 M0 Mc W (fun _ => False)).
      { apply eff_store; [|exact HMcg]. intros x HF HW. pose proof (u64_range x). apply HMcw; intros Hx. apply HW. unfold W, W_of, SS. cbn. lia. }
      assert (ROCc : img_ro_clear L Mc).
      { eapply (img_ro_clear_via_eff' A0 A0 M0 Mc model0 W _ ROC0 AI0 EFc); [intros a [] | unfold W; cbn; lia]. }
      assert (SXc : sx_inv ST s Mc).
      { eapply (sx_inv_via_eff' s A0 A0 M0 Mc model0 W _ (cb_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) AI0 EFc
                 (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB)); [intros a [] | unfold W; cbn; lia]. }
      replace (Z_to_bv 64 949044) with (Z_to_bv 64 (ly_new L) : word) by (rewrite HLnew; reflexivity).
      eapply (NEW fx A0 s Rc Mc model0 (8 * n) (sp - 32) NEWR K AIc MS0 ROCc SXc (cb_sxh _ _ _ _ _ _ _ _ _ _ _ _ CB)).
      - constructor; [exact G1 | apply bv_eq; vm_compute; reflexivity | unfold NEWR; lia | rewrite G2, w_addm by lia; f_equal; lia
                     | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16 | lia
                     | rewrite Gs by inl; exact Hgp | rewrite Gs by inl; exact Htp].
      - rewrite G10. rewrite w_mul by lia. first [reflexivity | f_equal; lia].
      - unfold LIB_NMAX in HNMAX. lia.
      - lia.
      - apply stack_room_of_defined; [lia | lia | lia |]. unfold Mc. repeat apply defined_wbytes.
        eapply defined_sub; [exact Hdef0 | lia | lia].
      - intros a Ha. split; [eapply hi_unowned; [exact AI0 | unfold zwin in Ha; lia]|]. apply (proj2 (Hwin0 a ltac:(unfold zwin in *; lia))).
      - exact (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB).
      - exact (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB).
      - replace (new_size (8 * n)) with (8 * n) by (unfold new_size; lia).
        eapply roomL_room_for; [exact AI0 | unfold LIB_NMAX in HNMAX; lia | exact ROOM].
      -
        intros A1 R1 M1 model1 p AI1 MS1 Hfs1 Hfds1 SX1 KEPT R1a0 Hp LADD CAPS BIGC NEWT FR DEF.
        replace (new_size (8 * n)) with (8 * n) in LADD, FR by (unfold new_size; lia).
        assert (EFF : eff MI A0 A1 Mc M1 (sp - 32 - NEW_STACK, sp - 32) (fun a => p <= a < p + 8 * n)).
        { eapply (eff_of_new MI A0 A1 Mc M1 model1); [exact AI1 | exact CAPS | exact BIGC | exact NEWT | exact FR | exact DEF | intros a Ha; exact Ha | intros a Ha; exact Ha]. }
        assert (HinP : In (p, 8 * n) (live MI A1)) by (rewrite (proj1 LADD); left; reflexivity).
        destruct (ai_live_block MI A1 M1 model1 p (8 * n) AI1 HinP) as (_ & Hpal & Hp0 & Hpc & Hpown).
        assert (AGf : agree_on Mc M1 (sp - 32) 32).
        { eapply (agree_above_via_eff' A0 A1 Mc M1 _ _ (sp - 32) 32 (sp - 32) EFF); [lia | cbn; lia | lia | lia | lia | | |].
          - intros i Hi. eapply hi_unowned; [exact AI0 | lia].
          - intros i Hi. apply HMcg. eapply (defined_pt _ _ _ _ Hdef0). lia.
          - intros i Hi Hf. cbn beta in Hf. lia. }
        apply (POST A1 M1 model1 R1 p AI1 MS1 Hfs1 Hfds1).
        + unfold base_ok. rewrite !(KEPT _) by inl. rewrite G2, !Gs by inl. rewrite w_addm by lia. replace (sp + -32) with (sp - 32) by lia.
          repeat split; try reflexivity; try assumption. intros r Hr. rewrite (KEPT r); [apply Gs|]; cbn in Hr; unfold callee_saved; repeat (destruct Hr as [<-|Hr]; [inl|]); destruct Hr.
        + exact R1a0.
        + rewrite (KEPT 8%bv) by inl. exact G8.
        + rewrite (KEPT 9%bv) by inl. exact G9.
        + unfold frame, cell8. split; [|split]; (eapply cellw_agree; [| eapply agree_on_sub; [exact AGf | lia | cbn; lia] | lia | cbn; lia]); unfold Mc; cellpeel.
        + eapply (defined_via_eff L MI HLimg_lo HLrw_img HLerr_rw A0 A1 Mc M1 _ _ (sp - SS) SS EFF ltac:(lia) ltac:(lia)).
          * intros i Hi. eapply hi_unowned; [exact AI0 | lia].
          * intros i Hi Hf. cbn beta in Hf. lia.
          * unfold Mc. repeat apply defined_wbytes. exact Hdef0.
        + exact Hp0. + exact Hpc. + exact Hpal. + exact LADD.
        + eapply eff_weaken; [eapply eff_trans; [exact EFc | eapply eff_widen; [exact EFF|] |]|].
          * intros a Ha. unfold W, W_of, SS in *. cbn in *. lia.
          * intros a Ha. eapply hi_unowned; [exact AI1 | unfold W, W_of in Ha; cbn in Ha; lia].
          * intros a [[]|Ha]. exact Ha.
        +
          eapply (umapx_via_eff L MI HLimg_lo HLrw_img HLerr_rw 24 _ (nval24 SEGS) ltac:(lia) (nval24_agree SEGS) A0 A1 M0 M1 model0 obj bl bc ents W _ sp U0 AI0).
          * eapply eff_weaken; [eapply eff_trans; [exact EFc | eapply eff_widen; [exact EFF|] |]|].
            -- intros a Ha. unfold W, W_of, SS in *. cbn in *. lia.
            -- intros a Ha. eapply hi_unowned; [exact AI1 | unfold W, W_of in Ha; cbn in Ha; lia].
            -- intros a [[]|Ha]. exact Ha.
          * lia. * unfold W; cbn; lia. * lia.
          * intros i Hi. eapply hi_unowned; [exact AI0 | lia].
          *
            intros a Ha Hpa. destruct (umap_foot_hb 24 obj bl bc ents a Ha) as [Hh | ([q m] & Hb & Hba)]; [lia|]. cbn in Hba.
            pose proof (tbl_blocks_live _ Hb) as Hq0.
            assert (Hq1 : In (q, m) (live MI A1)) by (rewrite (proj1 LADD); right; exact Hq0).
            assert (Hne : p <> q).
            { intros <-. apply (proj2 LADD). apply (in_map fst _ (p, m)). exact Hq0. }
            pose proof (ai_live_disjoint MI A1 M1 model1 p (8 * n) q m AI1 HinP Hq1 Hne) as Hap. lia.
          * unfold W, SS; cbn; lia.
          * intros q m Hb Hl. rewrite (proj1 LADD). right. exact Hl.
    Qed.

    Record rst (F : Z -> Prop) (ops : list lop) (p : Z) (A : AS MI) (M : mem) (model : Model) (R : bvmap 5 word) : Prop := RST {
      r_ai : ainv MI A M model;
      r_ms : mstd model;
      r_fs : m_fs model = m_fs model0;
      r_fds : m_fds model = m_fds model0;
      r_regs : base_ok R;
      r_s0 : getr R 8%bv = Z_to_bv 64 n;
      r_s1 : getr R 9%bv = Z_to_bv 64 obj;
      r_frame : frame M;
      r_def : defined M (sp - SS) SS;
      r_eff : eff MI A0 A M0 M W F;
      r_lap : lapply (live MI A0) ops (live MI A);
      r_p0 : 0 < p; r_pc : p + 8 * n <= alloc_ceiling; r_pal : p mod 16 = 0;
      r_plive : In (p, 8 * n) (live MI A);
      r_pnew : ~ In p (map fst (live MI A0));
      r_Foff : forall a, F a -> ~ in_ranges (ly_img L) a;
      r_hdef : defined M obj 40
    }.

    Definition FA (p : Z) (a : Z) : Prop := p <= a < p + 8 * n.
    Definition FB (p : Z) (a : Z) : Prop := FA p a \/ (obj <= a < obj + 8) \/ (bc <> 0 /\ bl <= a < bl + 8 * bc).
    Definition opsB (p : Z) : list lop := LAdd p (8 * n) :: (if bc =? 0 then [] else [LDel bl]).

    Lemma p_apart : forall p A M model b, ainv MI A M model -> live_add p (8 * n) (live MI A0) (live MI A) ->
      In b (umap_blocks 24 bl bc ents) -> apart p (8 * n) (fst b) (snd b).
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn fx A0 s R0 M0 model0 sp ret obj bl bc ents K CB U0 CONT.
      intros p A M model [q m] AI LADD Hb. cbn.
      pose proof (tbl_blocks_live _ Hb) as Hq0.
      assert (Hq1 : In (q, m) (live MI A)) by (rewrite (proj1 LADD); right; exact Hq0).
      assert (HinP : In (p, 8 * n) (live MI A)) by (rewrite (proj1 LADD); left; reflexivity).
      assert (Hne : p <> q) by (intros <-; apply (proj2 LADD); apply (in_map fst _ (p, m)); exact Hq0).
      exact (ai_live_disjoint MI A M model p (8 * n) q m AI HinP Hq1 Hne).
    Qed.

    Lemma phaseB : forall A1 M1 model1 R1 p,
      rst (FA p) [LAdd p (8 * n)] p A1 M1 model1 R1 -> getr R1 10%bv = Z_to_bv 64 p ->
      umapx MI 24 (nval24 SEGS) A1 M1 obj bl bc ents ->
      (forall A2 M2 model2 R2,
          rst (FB p) (opsB p) p A2 M2 model2 R2 ->
          cell8 SEGS M2 obj p ->

          agree_on M1 M2 (obj + 8) 32 -> (forall q k v, In (q, (k, v)) ents -> agree_on M1 M2 q 24 /\ In (q, 24) (live MI A2)) ->
          srealizes SEGS (cfg fx R2 C_PC M2 model2) K) ->
      srealizes SEGS (cfg fx R1 NEWR M1 model1) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc ents K CB U0 Hlast ASP CONT.
      intros A1 M1 model1 R1 p D G10 U1 POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      destruct ASP as (Hs1 & Hh1 & Ho1).
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq U0) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B S0 S1 FR DEF EFF LAP Hp0 Hpc Hpal Hpl Hpnew HFoff HDEF]. destruct B as (B2 & B3 & B4 & Bs).
      pose proof (u_hdr U1) as HD. destruct HD as [Cbl Cbc Cp1 Csz Cmlf Cdef]. unfold cell8 in Cbl, Cbc. unfold cell4 in Cmlf.
      pose proof (proj1 Cbl) as Hblr. pose proof (proj1 Cbc) as Hbcr.
      pose (E := Eseed R1 [Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 (sp - 32); Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                           Z_to_bv 64 bl; Z_to_bv 64 bc]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (9%bv, EVar 33); (2%bv, EVar 34); (8%bv, EVar 35)]) R1).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M1 []) by constructor.
      assert (Hdefobj : defined M1 obj 40) by exact Cdef.
      destruct (Z.eq_dec bc 0) as [Hz | Hnz].
      -
        assert (Hbl0 : bl = 0) by (destruct (u_blive U1) as [[_ H]|[H _]]; [exact H | exfalso; exact (H Hz)]).
        rewrite Hbl0 in *.
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. sc_so. eapply (defined_sub _ _ _ _ _ Hdefobj); lia. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        set (Mw := wbytes M1 _ _).
        rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 9%bv G9.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
        pose proof (u64_range (getr R0 8)) as Hr8. pose proof (u64_range (getr R0 9)) as Hr9.
        assert (HMw : forall x : word, ~ (obj <= bv_unsigned x < obj + 8) -> Mw x = M1 x).
        { intros x Hx. pose proof (u64_range x). unfold Mw.
          rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMg : forall x : word, M1 x <> None -> Mw x <> None) by (intros x Hx; unfold Mw; apply wbytes_grows; exact Hx).
        assert (HMa : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k obj 8 -> agree_on M1 Mw a k).
        { intros a k Ha Hak H1 i Hi. apply HMw; rewrite u64_of_Z by lia; unfold apart in *; lia. }
        apply (POST A1 Mw model1 Rc).
        + constructor.
          * eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
            intros x Ho. pose proof (u64_range x). apply HMw; intros Hx. exact (hi_unowned A1 M1 model1 (bv_unsigned x) AI ltac:(lia) Ho).
          * exact MS. * exact Hfs. * exact Hfds.
          * unfold base_ok. rewrite G2, !Gs by inl. repeat split; try assumption. intros r Hr. rewrite Gs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
          * exact G8. * exact G9.
          * destruct FR as (F1 & F2 & F3). unfold frame. unfold SS in *.
            split; [|split]; (eapply cellw_agree; [eassumption | apply HMa; unfold apart; cbn; lia | lia | cbn; lia]).
          * eapply defined_agree; [exact DEF | apply HMa; unfold apart, SS in *; lia].
          * eapply eff_weaken; [eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned; [exact AI | unfold W, W_of in Ha; cbn in Ha; lia]]|].
            -- eapply eff_store with (F := fun a : Z => obj <= a < obj + 8); [|exact HMg]. intros x HF HW. apply HMw. exact HF.
            -- intros a [Ha|Ha]; [left; exact Ha | right; left; exact Ha].
          * unfold opsB. rewrite (proj2 (Z.eqb_eq _ _) Hz). exact LAP.
          * exact Hp0. * exact Hpc. * exact Hpal. * exact Hpl. * exact Hpnew.
          * intros a [Ha|[Ha|[Ha _]]]; [exact (HFoff a Ha) | intros Himg; pose proof (HLimg_lo _ Himg); unfold SS in Hsplo; lia | exfalso; exact (Ha Hz)].
          * intros i Hi. apply HMg. apply Hdefobj. exact Hi.
        + unfold cell8, Mw. cellpeel.
        + apply HMa; unfold apart; lia.
        + intros q k v Hin. destruct (u_node U1 q k v Hin) as (Hlv & Hq0 & Hq1 & _).
          destruct (live_facts' A1 M1 model1 q 24 AI Hlv) as (_ & _ & Hqc & _).
          split; [apply HMa; unfold apart; lia | exact Hlv].
      -
        assert (Hblp : 0 < bl) by exact (u_bl_lo U1 Hnz).
        assert (Hbllive : In (bl, 8 * bc) (live MI A1)) by (destruct (u_blive U1) as [[? ?]|[_ H]]; [lia | exact H]).
        destruct (live_facts' A1 M1 model1 bl (8 * bc) AI Hbllive) as (_ & _ & Hblc & _).
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_so. eapply (defined_sub _ _ _ _ _ Hdefobj); lia. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        set (Mw := wbytes M1 _ _).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 9%bv G9. rreg HRc 10%bv G10'.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
        pose proof (u64_range (getr R0 8)) as Hr8. pose proof (u64_range (getr R0 9)) as Hr9.
        assert (HMw : forall x : word, ~ (obj <= bv_unsigned x < obj + 8) -> Mw x = M1 x).
        { intros x Hx. pose proof (u64_range x). unfold Mw.
          rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMg : forall x : word, M1 x <> None -> Mw x <> None) by (intros x Hx; unfold Mw; apply wbytes_grows; exact Hx).
        assert (HMa : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k obj 8 -> agree_on M1 Mw a k).
        { intros a k Ha Hak H1 i Hi. apply HMw; rewrite u64_of_Z by lia; unfold apart in *; lia. }
        assert (AIw : ainv MI A1 Mw model1).
        { eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
          intros x Ho. pose proof (u64_range x). apply HMw; intros Hx. exact (hi_unowned A1 M1 model1 (bv_unsigned x) AI ltac:(lia) Ho). }
        assert (EFw : eff MI A0 A1 M0 Mw W (fun a => FA p a \/ (obj <= a < obj + 8))).
        { eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned; [exact AI | unfold W, W_of in Ha; cbn in Ha; lia]].
          eapply eff_store with (F := fun a : Z => obj <= a < obj + 8); [|exact HMg]. intros x HF HW. apply HMw. exact HF. }
        assert (ROCw : img_ro_clear L Mw).
        { eapply (img_ro_clear_via_eff' A0 A1 M0 Mw model0 W _ ROC0 AI0 EFw); [| unfold W; cbn; lia].
          intros a [Ha|Ha]; [exact (HFoff a Ha) | intros Himg; pose proof (HLimg_lo _ Himg); unfold SS in Hsplo; lia]. }
        eapply (del_call fx A1 Mw model1 Rc bl (8 * bc) (sp - 32) DRET K AIw MS ROCw G1);
          [ apply bv_eq; vm_compute; reflexivity | unfold DRET; lia | exact G2
          | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16 | lia
          | rewrite Gs by inl; exact B3 | rewrite Gs by inl; exact B4 | exact G10'
          | right; exact Hbllive
          | unfold SS in *; lia | unfold SS in *; lia
          | intros i Hi; apply HMg; eapply (defined_pt _ _ _ _ DEF); unfold SS in *; lia
          | intros a Ha; eapply hi_unowned; [exact AI | unfold zwin in Ha; lia] | ].
        intros A2 R2 M2 model2 AI2 MS2 Hfs2 Hfds2 KEPT LDEL EFF2 DEF2 WIN2.
        assert (AG2 : forall a k, 0 <= k -> alloc_ceiling <= a -> (a + k <= sp - 32 - DEL_STACK \/ sp - 32 <= a) -> a + k <= 2 ^ 47 -> defined Mw a k -> agree_on Mw M2 a k).
        { intros a k Hk Ha Hw Hak Hd i Hi. apply (ef_frame _ _ _ _ _ _ _ _ _ EFF2). rewrite u64_of_Z by lia.
          intros [Ho|[Ho'|[Hnm|[Hf|[Hw'|He]]]]].
          - exact (hi_unowned A1 Mw model1 (a + i) AIw ltac:(lia) Ho).
          - exact (hi_unowned A2 M2 model2 (a + i) AI2 ltac:(lia) Ho').
          - destruct Hnm as (_ & _ & Hn0). exact (Hd i Hi Hn0).
          - cbn beta in Hf. lia.
          - unfold W_of in Hw'. cbn in Hw'. lia.
          - pose proof (HLimg_lo _ (HLrw_img _ (HLerr_rw _ He))). lia. }
        assert (AGobj : agree_on Mw M2 obj 40).
        { apply AG2; [lia | lia | lia | lia |]. intros i Hi. apply HMg. apply Hdefobj. exact Hi. }
        assert (Cbl2 : cell8 SEGS M2 obj p).
        { eapply cellw_agree; [| eapply agree_on_sub; [exact AGobj | lia | cbn; lia] | lia | cbn; lia]. unfold Mw. cellpeel. }
        apply (POST A2 M2 model2 R2).
        + constructor.
          * exact AI2. * exact MS2. * congruence. * congruence.
          * unfold base_ok. rewrite !(KEPT _) by inl. rewrite G2, !Gs by inl. repeat split; try assumption.
            intros r Hr. rewrite (KEPT r); [rewrite Gs; [apply Bs, Hr|] |]; cbn in Hr; unfold callee_saved; repeat (destruct Hr as [<-|Hr]; [inl|]); destruct Hr.
          * rewrite (KEPT 8%bv) by inl. exact G8.
          * rewrite (KEPT 9%bv) by inl. exact G9.
          * destruct FR as (F1 & F2 & F3). unfold frame. unfold SS in *.
            split; [|split]; (eapply cellw_agree; [| apply AG2; [lia | lia | lia | lia |] | lia | cbn; lia]);
              [ | intros i Hi; apply HMg; eapply (defined_pt _ _ _ _ DEF); lia
              | | intros i Hi; apply HMg; eapply (defined_pt _ _ _ _ DEF); lia
              | | intros i Hi; apply HMg; eapply (defined_pt _ _ _ _ DEF); lia ];
              (eapply cellw_agree; [eassumption | apply HMa; unfold apart; cbn; lia | lia | cbn; lia]).
          *
            intros i Hi.
            destruct (Z.lt_ge_cases (sp - SS + i) (sp - 32 - DEL_STACK)) as [Hlo | Hhi].
            -- pose proof (AG2 (sp - SS + i) 1 ltac:(lia) ltac:(unfold SS in *; lia) ltac:(lia) ltac:(lia)) as E1.
               assert (Hd : defined Mw (sp - SS + i) 1) by (intros j Hj; apply HMg; eapply (defined_pt _ _ _ _ DEF); lia).
               specialize (E1 Hd 0 ltac:(lia)). rewrite Z.add_0_r in E1. rewrite E1. apply HMg. eapply (defined_pt _ _ _ _ DEF); lia.
            -- destruct (Z.lt_ge_cases (sp - SS + i) (sp - 32)) as [Hm | Hh].
               ++ replace (sp - SS + i) with (sp - 32 - DEL_STACK + (sp - SS + i - (sp - 32 - DEL_STACK))) by lia. apply DEF2. lia.
               ++ pose proof (AG2 (sp - SS + i) 1 ltac:(lia) ltac:(unfold SS in *; lia) ltac:(lia) ltac:(lia)) as E1.
                  assert (Hd : defined Mw (sp - SS + i) 1) by (intros j Hj; apply HMg; eapply (defined_pt _ _ _ _ DEF); lia).
                  specialize (E1 Hd 0 ltac:(lia)). rewrite Z.add_0_r in E1. rewrite E1. apply HMg. eapply (defined_pt _ _ _ _ DEF); lia.
          * eapply eff_weaken; [eapply eff_trans; [exact EFw | eapply eff_widen; [exact EFF2|] | ]|].
            -- intros a Ha. unfold W, W_of, SS in *. cbn in *. lia.
            -- intros a Ha. eapply hi_unowned; [exact AI2 | unfold W, W_of in Ha; cbn in Ha; lia].
            -- intros a [[Ha|Ha]|Ha]; [left; exact Ha | right; left; exact Ha | right; right; split; [exact Hnz | exact Ha]].
          * unfold opsB. destruct (Z.eqb_spec bc 0); [lia|]. cbn in LAP. destruct LAP as (lv1 & Hadd & Heq). cbn.
            exists lv1. split; [exact Hadd|]. exists (live MI A2). split; [rewrite <- Heq; exact LDEL | reflexivity].
          * exact Hp0. * exact Hpc. * exact Hpal.
          * apply (proj2 (LDEL p (8 * n))). split; [exact Hpl|]. intros ->. apply Hpnew.
            apply (in_map fst _ (bl, 8 * bc)). apply tbl_blocks_live. unfold umap_blocks. destruct (Z.eqb_spec bc 0); [lia|]. apply in_app_iff. left. left. reflexivity.
          * exact Hpnew.
          * intros a [Ha|[Ha|[_ Ha]]]; [exact (HFoff a Ha) | intros Himg; pose proof (HLimg_lo _ Himg); unfold SS in Hsplo; lia |].
            exact (live_offimg' A1 M1 model1 bl (8 * bc) a AI Hbllive Ha).
          * eapply defined_agree; [| exact AGobj]. intros i Hi. apply HMg. apply Hdefobj. exact Hi.
        + exact Cbl2.
        + eapply agree_on_trans; [apply HMa; unfold apart; lia | eapply agree_on_sub; [exact AGobj | lia | lia]].
        + intros q k v Hin. destruct (u_node U1 q k v Hin) as (Hlv & Hq0 & Hq1 & _ & _ & _ & _ & _ & _ & Hapb).
          destruct (live_facts' A1 M1 model1 q 24 AI Hlv) as (_ & _ & Hqc & Hqown). specialize (Hapb Hnz).
          assert (Hlv2 : In (q, 24) (live MI A2)).
          { apply (proj2 (LDEL q 24)). split; [exact Hlv|]. intros ->. unfold apart in Hapb. lia. }
          split; [| exact Hlv2].
          eapply agree_on_trans; [apply HMa; unfold apart; lia |].
          destruct (live_facts' A2 M2 model2 q 24 AI2 Hlv2) as (_ & _ & _ & Hqown2).
          intros i Hi. apply (ef_frame _ _ _ _ _ _ _ _ _ EFF2). rewrite u64_of_Z by lia.
          intros [Ho|[Ho'|[Hnm|[Hf|[Hw'|He]]]]].
          * exact (proj1 (Hqown (q + i) ltac:(lia)) Ho).
          * exact (proj1 (Hqown2 (q + i) ltac:(lia)) Ho').
          * destruct Hnm as (_ & _ & Hn0). exact (HMg _ (proj2 (Hqown (q + i) ltac:(lia))) Hn0).
          * cbn beta in Hf. unfold apart in Hapb. lia.
          * unfold W_of in Hw'. cbn in Hw'. lia.
          * exact (live_offimg' A1 M1 model1 q 24 (q + i) AI Hlv ltac:(lia) (HLrw_img _ (HLerr_rw _ He))).
    Qed.

    Definition FC (p : Z) (a : Z) : Prop := FB p a \/ (obj + 8 <= a < obj + 16).

    Lemma zloop : forall (k : nat) p i Mi R (Mw : mem) model,
      Z.of_nat k = n - i -> 0 <= i < n -> 0 < p -> p + 8 * n <= alloc_ceiling -> p mod 16 = 0 -> mstd model ->
      base_ok R -> getr R 8%bv = Z_to_bv 64 n -> getr R 9%bv = Z_to_bv 64 obj -> getr R 10%bv = Z_to_bv 64 p ->
      getr R 11%bv = Z_to_bv 64 (8 * i) -> getr R 12%bv = Z_to_bv 64 i -> getr R 13%bv = Z_to_bv 64 0 -> getr R 14%bv = Z_to_bv 64 (p + 8 * i) ->
      getr R 15%bv = Z_to_bv 64 (2 ^ 64 - 1 - p) ->
      (forall x : word, ~ (p <= bv_unsigned x < p + 8 * n) -> Mi x = Mw x) -> (forall x : word, Mw x <> None -> Mi x <> None) ->
      (forall j, 0 <= j < i -> cell8 SEGS Mi (p + 8 * j) 0) -> defined Mi p (8 * n) ->
      (forall M' R', base_ok R' -> getr R' 8%bv = Z_to_bv 64 n -> getr R' 9%bv = Z_to_bv 64 obj -> getr R' 10%bv = Z_to_bv 64 p ->
          getr R' 15%bv = Z_to_bv 64 (2 ^ 64 - 1 - p) ->
          (forall x : word, ~ (p <= bv_unsigned x < p + 8 * n) -> M' x = Mw x) -> (forall x : word, Mw x <> None -> M' x <> None) ->
          (forall j, 0 <= j < n -> cell8 SEGS M' (p + 8 * j) 0) ->
          srealizes SEGS (cfg fx R' D_PC M' model) K) ->
      srealizes SEGS (cfg fx R ZL_PC Mi model) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn fx A0 s R0 M0 model0 sp ret obj bl bc ents K CB U0 Hlast.
      induction k as [|k IH]; intros p i Mi R Mw model Hk Hi Hp0 Hpc Hpal MS B Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 HM HG HZ DEFp POST; [lia|].
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof B as B'. destruct B' as (B2 & B3 & B4 & Bs). pose proof (u_obj_hi U0) as Hobjhi. pose proof (u_obj_lo U0) as Hobjlo.
      destruct n_facts as (HnB & Hbcn & Hn28 & _).
      pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 0; Z_to_bv 64 (sp - 32); Z_to_bv 64 n; Z_to_bv 64 p; Z_to_bv 64 (8 * i); Z_to_bv 64 i; Z_to_bv 64 (p + 8 * i);
                          Z_to_bv 64 (2 ^ 64 - 1 - p)]).
      assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 32); (2%bv, EVar 34); (8%bv, EVar 35); (10%bv, EVar 36); (11%bv, EVar 37); (12%bv, EVar 38); (13%bv, ELit 0); (14%bv, EVar 39); (15%bv, EVar 40)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E Mi []) by constructor.
      Ltac scZ DEFp p i :=
        split_scs; try sc_auto1;
        first [ eapply (sc_trap_srl _ _ _ _ i 60); [evs; reflexivity | lia | lia]
              | eapply (sc_trap_notlt _ _ _ _ _ p (8 * i)); [evs; reflexivity | evs; reflexivity | lia | lia | lia]
              | sc_so; eapply (defined_sub _ _ _ _ _ DEFp); lia
              | cbn [sc_denot]; evs; nadd; rewrite ?br_ne by lia; bool_lia
              | idtac ].

      assert (NEXT : forall Mn, Mn = wbytes Mi (Z_to_bv 64 (p + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
        (forall x : word, ~ (p <= bv_unsigned x < p + 8 * n) -> Mn x = Mw x) /\ (forall x : word, Mw x <> None -> Mn x <> None)
        /\ (forall j, 0 <= j < i + 1 -> cell8 SEGS Mn (p + 8 * j) 0) /\ defined Mn p (8 * n)).
      { intros Mn ->. split; [| split; [| split]].
        - intros x Hx. pose proof (u64_range x). rewrite wbytes_outside; [apply HM; exact Hx | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia.
        - intros x Hx. apply wbytes_grows. apply HG. exact Hx.
        - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [unfold cell8; cellpeel|].
          unfold cell8. apply cellw_wb_other; [apply HZ; lia | lia | rewrite length_N_to_le_bytes; change (Z.of_nat 8) with 8; lia | lia | cbn; lia | rewrite length_N_to_le_bytes; change (Z.of_nat 8) with 8; unfold apart; lia].
        - intros j Hj. apply wbytes_grows. apply DEFp. exact Hj. }
      destruct (Z.eq_dec (i + 1) n) as [Hfin | Hmore].
      -
        xruns HR HK 100%nat STOPS (SCR [false; false; false] [] []) 50%N; [scZ DEFp p i|].
        postrun. rewrite ?w_add by lia.
        destruct (NEXT _ eq_refl) as (HM' & HG' & HZ' & DEF').
        apply (POST _ R'); [ unfold base_ok; rreg HR' 2%bv T2; rewrite T2; split; [reflexivity|]; split; [exact (eq_trans (syms_id_sound _ _ _ _ [3]%bv HR' eq_refl 3%bv ltac:(inl)) B3)|];
                               split; [exact (eq_trans (syms_id_sound _ _ _ _ [4]%bv HR' eq_refl 4%bv ltac:(inl)) B4)|];
                               intros r Hr; rewrite (syms_id_sound _ _ _ _ [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl r Hr); apply Bs; exact Hr
                           | rreg HR' 8%bv T; exact T | rreg HR' 9%bv T; exact T | rreg HR' 10%bv T; exact T | rreg HR' 15%bv T; exact T
                           | exact HM' | exact HG' | rewrite <- Hfin; exact HZ' ].
      -
        xruns HR HK 100%nat STOPS (SCR [false; false; true] [] []) 50%N; [scZ DEFp p i|].
        postrun. rewrite ?w_add by lia.
        destruct (NEXT _ eq_refl) as (HM' & HG' & HZ' & DEF').
        eapply (IH p (i + 1) _ R' Mw model ltac:(lia) ltac:(lia) Hp0 Hpc Hpal MS);
          [ unfold base_ok; rreg HR' 2%bv T2; rewrite T2; split; [reflexivity|]; split; [exact (eq_trans (syms_id_sound _ _ _ _ [3]%bv HR' eq_refl 3%bv ltac:(inl)) B3)|];
            split; [exact (eq_trans (syms_id_sound _ _ _ _ [4]%bv HR' eq_refl 4%bv ltac:(inl)) B4)|];
            intros r Hr; rewrite (syms_id_sound _ _ _ _ [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl r Hr); apply Bs; exact Hr
          | rreg HR' 8%bv T; exact T | rreg HR' 9%bv T; exact T | rreg HR' 10%bv T; exact T
          | rreg HR' 11%bv T; rewrite T; nadd; f_equal; lia
          | rreg HR' 12%bv T; rewrite T; nadd; reflexivity
          | rreg HR' 13%bv T; exact T
          | rreg HR' 14%bv T; rewrite T; nadd; f_equal; lia
          | rreg HR' 15%bv T; exact T
          | exact HM' | exact HG' | exact HZ' | exact DEF' | exact POST ].
    Qed.

    Lemma phaseC : forall A1 M1 A2 M2 model2 R2 p,
      rst (FB p) (opsB p) p A2 M2 model2 R2 ->
      umapx MI 24 (nval24 SEGS) A1 M1 obj bl bc ents ->
      cell8 SEGS M2 obj p -> agree_on M1 M2 (obj + 8) 32 ->
      (forall q k v, In (q, (k, v)) ents -> agree_on M1 M2 q 24 /\ In (q, 24) (live MI A2)) ->
      (forall M3 R3,
          rst (FC p) (opsB p) p A2 M3 model2 R3 -> getr R3 10%bv = Z_to_bv 64 p -> getr R3 15%bv = Z_to_bv 64 (2 ^ 64 - 1 - p) ->
          cell8 SEGS M3 obj p -> cell8 SEGS M3 (obj + 8) n -> agree_on M1 M3 (obj + 16) 24 ->
          (forall q k v, In (q, (k, v)) ents -> agree_on M1 M3 q 24 /\ In (q, 24) (live MI A2)) ->
          (forall i, 0 <= i < n -> cell8 SEGS M3 (p + 8 * i) 0) ->
          srealizes SEGS (cfg fx R3 D_PC M3 model2) K) ->
      srealizes SEGS (cfg fx R2 C_PC M2 model2) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn HLimg_lo HLrw_img fx A0 s R0 M0 model0 sp ret obj bl bc ents K CB U0 Hlast ASP CONT.
      intros A1 M1 A2 M2 model2 R2 p D U1 Cbl AGh Hnodes POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hs1 & Hh1 & Ho1).
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq U0) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B S0 S1 FR DEF EFF LAP Hp0 Hpc Hpal Hpl Hpnew HFoff HDEF]. destruct B as (B2 & B3 & B4 & Bs).
      pose proof HDEF as Hdefobj. unfold cell8 in Cbl. pose proof (proj1 Cbl) as Hpr.
      pose (E := Eseed R2 [Z_to_bv 64 obj; Z_to_bv 64 0; Z_to_bv 64 (sp - 32); Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 p]).
      assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 32); (2%bv, EVar 34); (8%bv, EVar 35)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M2 []) by constructor.
      xruns HR HK 100%nat STOPS (SCR [false; false] [EVar 40] []) 50%N.
      { split_scs; try sc_auto1; first [ eapply (sc_trap_null _ _ _ _ p); [evs; reflexivity | lia] | sc_so; eapply (defined_sub _ _ _ _ _ Hdefobj); lia | idtac ]. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
      set (Mw := wbytes M2 _ _).
      rreg HRc 2%bv T2. rreg HRc 8%bv T8. rreg HRc 9%bv T9. rreg HRc 10%bv T10. rreg HRc 11%bv T11. rreg HRc 12%bv T12. rreg HRc 13%bv T13. rreg HRc 14%bv T14. rreg HRc 15%bv T15.
      rewrite w_and, land_7, (align16_8 p Hpal) in T13 by lia. rewrite w_notexpr in T15 by lia.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Ts.
      pose proof (u64_range (getr R0 8)) as Hr8. pose proof (u64_range (getr R0 9)) as Hr9.
      assert (HMw : forall x : word, ~ (obj + 8 <= bv_unsigned x < obj + 16) -> Mw x = M2 x).
      { intros x Hx. pose proof (u64_range x). unfold Mw.
        rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
      assert (HMg : forall x : word, M2 x <> None -> Mw x <> None) by (intros x Hx; unfold Mw; apply wbytes_grows; exact Hx).
      assert (HMa : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k (obj + 8) 8 -> agree_on M2 Mw a k).
      { intros a k Ha Hak H1 i Hi. apply HMw; rewrite u64_of_Z by lia; unfold apart in *; lia. }
      destruct (ai_live_block MI A2 M2 model2 p (8 * n) AI Hpl) as (_ & _ & _ & _ & Hpown).
      assert (Bc : base_ok Rc).
      { unfold base_ok. rewrite T2, !Ts by inl. repeat split; try assumption. intros r Hr. rewrite Ts; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr. }
      apply (zloop (Z.to_nat n) p 0 Mw Rc Mw model2 ltac:(lia) ltac:(lia) Hp0 Hpc Hpal MS Bc T8 T9 T10 ltac:(rewrite T11; reflexivity) T12 T13 ltac:(rewrite T14; f_equal; lia) T15
               ltac:(intros x _; reflexivity) ltac:(intros x Hx; exact Hx) ltac:(intros j Hj; lia)
               ltac:(intros i Hi; apply HMg; exact (proj2 (proj2 (Hpown (p + i) ltac:(lia)))))).
      intros M3 R4 BR4 Q8 Q9 Q10 Q15 HM3 HM3g Hz.
      assert (HM3a : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k p (8 * n) -> agree_on Mw M3 a k).
      { intros a k Ha Hak H1 i Hi. apply HM3; rewrite u64_of_Z by lia; unfold apart in *; lia. }
      apply (POST M3 R4).
      - constructor.
        + eapply (ai_frame MI); [exact AI | | intros x Hx; apply HM3g, HMg, Hx | reflexivity | reflexivity].
          intros x Ho. pose proof (u64_range x). rewrite HM3; [apply HMw|]; intros Hx.
          * exact (hi_unowned A2 M2 model2 (bv_unsigned x) AI ltac:(lia) Ho).
          * exact (proj1 (Hpown (bv_unsigned x) Hx) Ho).
        + exact MS. + exact Hfs. + exact Hfds.
        + exact BR4. + exact Q8. + exact Q9.
        + destruct FR as (F1 & F2 & F3). unfold frame. unfold SS in *.
          split; [|split]; (eapply cellw_agree; [| eapply agree_on_trans; [apply HMa | apply HM3a]; unfold apart; cbn; lia | lia | cbn; lia]; assumption).
        + eapply defined_agree; [exact DEF | eapply agree_on_trans; [apply HMa | apply HM3a]; unfold apart, SS in *; lia].
        + eapply eff_weaken; [eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned; [exact AI | unfold W, W_of in Ha; cbn in Ha; lia]]|].
          * eapply eff_store with (F := fun a : Z => (obj + 8 <= a < obj + 16) \/ (p <= a < p + 8 * n)); [| intros x Hx; apply HM3g, HMg, Hx].
            intros x HF HW. rewrite HM3; [apply HMw|]; intros Hx; apply HF; [left; exact Hx | right; exact Hx].
          * intros a [Ha|[Ha|Ha]]; [left; exact Ha | right; exact Ha | left; left; exact Ha].
        + exact LAP.
        + exact Hp0. + exact Hpc. + exact Hpal. + exact Hpl. + exact Hpnew.
        + intros a [Ha|Ha]; [exact (HFoff a Ha) | intros Himg; pose proof (HLimg_lo _ Himg); unfold SS in Hsplo; lia].
        + intros i Hi. apply HM3g, HMg. apply Hdefobj. exact Hi.
      - exact Q10. - exact Q15.
      - eapply cellw_agree; [exact Cbl | eapply agree_on_trans; [apply HMa | apply HM3a]; unfold apart; cbn; lia | lia | cbn; lia].
      - unfold cell8. eapply cellw_agree; [| apply HM3a; unfold apart; cbn; lia | lia | cbn; lia]. unfold Mw. cellpeel.
      - eapply agree_on_trans; [eapply agree_on_sub; [exact AGh | lia | lia] | eapply agree_on_trans; [apply HMa | apply HM3a]; unfold apart; lia].
      - intros q k v Hin. destruct (Hnodes q k v Hin) as [Hag Hlv]. split; [| exact Hlv].
        destruct (u_node U1 q k v Hin) as (_ & Hq0 & Hq1 & _).
        assert (Hne : p <> q).
        { intros <-. apply Hpnew. apply (in_map fst _ (p, 24)). apply tbl_blocks_live. unfold umap_blocks. apply in_app_iff. right.
          apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin]. }
        pose proof (ai_live_disjoint MI A2 M2 model2 p (8 * n) q 24 AI Hpl Hlv Hne) as Hap.
        destruct (live_facts' A2 M2 model2 q 24 AI Hlv) as (_ & _ & Hqc & _). unfold SS in Hsplo.
        eapply agree_on_trans; [exact Hag | eapply agree_on_trans; [apply HMa | apply HM3a]; unfold apart in *; lia].
      - exact Hz.
    Qed.

    #[local] Notation lent := (Z * (Z * Z))%type.
    Definition d0 : lent := (0, (0, 0)).
    #[local] Notation addr := (HRehashModel.addr Z).
    #[local] Notation hkey := (HRehashModel.hkey Z).
    #[local] Notation hh := (HRehashModel.hh Z n).
    #[local] Notation snt := (obj + 16).

    Lemma sc_disjZ : forall M E (sa1 sa2 : saddr) (b1 b2 n1 n2 : Z),
      edenot E (a_base sa1) = Z_to_bv 64 b1 -> edenot E (a_base sa2) = Z_to_bv 64 b2 ->
      0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 -> 0 < n1 < 2 ^ 64 -> 0 < n2 < 2 ^ 64 ->
      0 <= b1 + a_off sa1 -> b1 + a_off sa1 + n1 <= 2 ^ 64 -> 0 <= b2 + a_off sa2 -> b2 + a_off sa2 + n2 <= 2 ^ 64 ->
      (b1 + a_off sa1 + n1 <= b2 + a_off sa2 \/ b2 + a_off sa2 + n2 <= b1 + a_off sa1) ->
      sc_denot SEGS M E (SCDisj sa1 (ELit n1) sa2 (ELit n2)).
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn A0 s R0 M0 model0 sp ret CB.
      intros M E sa1 sa2 b1 b2 n1 n2 H1 H2 Hb1 Hb2 Hn1 Hn2 Ho1 Ho1' Ho2 Ho2' Hd.
      cbn [sc_denot]. unfold flat, estart, elenZ. cbn [edenot]. rewrite H1, H2, !u64_of_Z by lia. lia.
    Qed.

    Record lst (p : Z) (M1 : mem) (P S : list lent) (B : Z -> Z) (A : AS MI) (M : mem) (R : bvmap 5 word) : Prop := LST {
      l_regs : base_ok R;
      l_x8 : getr R 10%bv = Z_to_bv 64 p;
      l_x9 : getr R 8%bv = Z_to_bv 64 n;
      l_x18 : getr R 9%bv = Z_to_bv 64 snt;
      l_x10 : getr R 11%bv = Z_to_bv 64 (addr (last P d0));
      l_x12 : getr R 15%bv = Z_to_bv 64 (hdaddr S);
      l_x11 : getr R 14%bv = Z_to_bv 64 (hh (last P d0));
      l_c12 : 2 <= bv_unsigned (getr R 12%bv);
      l_c13 : getr R 13%bv = Z_to_bv 64 (n - 1);
      l_c16 : S <> [] -> getr R 16%bv = Z_to_bv 64 1;
      l_c17 : S <> [] -> getr R 17%bv = Z_to_bv 64 (2 ^ 60);
      l_perm : Permutation (P ++ S) ents;
      l_binv : binv Z n snt P B;
      l_P : P <> [];
      l_p1 : cell8 SEGS M snt (hdaddr (P ++ S));
      l_chain : chain SEGS M (P ++ S);
      l_hash : forall e, In e ents -> cell8 SEGS M (addr e + 8) (hkey e);
      l_tail : forall e, In e ents -> agree_on M1 M (addr e + 8) 16;
      l_bkt : forall i, 0 <= i < n -> cell8 SEGS M (p + 8 * i) (B i);
      l_defp : defined M p (8 * n);
      l_defh : defined M obj 40;
      l_defn : forall e, In e ents -> defined M (addr e) 24;
      l_live : forall e, In e ents -> In (addr e, 24) (live MI A);
      l_plive : In (p, 8 * n) (live MI A)
    }.

    Definition Wloop (p : Z) (a : Z) : Prop :=
      (p <= a < p + 8 * n) \/ (snt <= a < snt + 8) \/ (exists e, In e ents /\ addr e <= a < addr e + 8).

    Lemma ent_facts : forall A1 M1 e, umapx MI 24 (nval24 SEGS) A1 M1 obj bl bc ents -> In e ents ->
      0 < addr e /\ addr e + 24 <= 2 ^ 47 /\ addr e mod 16 = 0 /\ 0 <= hkey e < 2 ^ 32.
    Proof using AC L MI sp obj bl bc ents.
      intros A1 M1 [q [k v]] U Hin. destruct (u_node U q k v Hin) as (_ & Hq0 & Hq1 & Hal & _ & _ & Hkr & _). cbn. lia.
    Qed.

    Ltac rdx Hh H := eapply (sc_read_cellw _ _ _ _ _ _ _ _ H);
      [ cbn; lia | evs; rewrite ?w_remu, ?w_mul, ?w_add by lia; rewrite ?v_addi_Z by lia; rewrite ?Hh; first [reflexivity | f_equal; lia] | evs; first [reflexivity | f_equal; lia] ].

    Lemma last_any : forall {X : Type} (l : list X) a b, l <> [] -> last l a = last l b.
    Proof using.
      intros X l a b Hne. induction l as [|q l IH]; [exfalso; exact (Hne eq_refl)|].
      destruct l as [|r l']; [reflexivity|]. cbn. cbn in IH. apply IH. discriminate.
    Qed.

    Definition hda (L : list lent) (t : Z) : Z := match L with [] => t | b :: _ => addr b end.
    Fixpoint lnk (M : mem) (Ls : list lent) (t : Z) : Prop :=
      match Ls with
      | [] => True
      | a :: Ls' => cell8 SEGS M (addr a) (hda Ls' t) /\ lnk M Ls' t
      end.

    Lemma lnk_chain : forall M Ls, chain SEGS M Ls <-> lnk M Ls 0.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret CB.
      intros M Ls. induction Ls as [|[a v] Ls IH]; cbn; [tauto|].
      destruct Ls as [|[b v'] Ls']; cbn in *; tauto.
    Qed.

    Lemma hd_app : forall (A B : list lent) t, hda (A ++ B) t = hda A (hda B t).
    Proof using. intros [|a A] B t; reflexivity. Qed.

    Lemma hdaddr_hda : forall (A : list lent), hdaddr A = hda A 0.
    Proof using. intros [|[a v] A]; reflexivity. Qed.

    Lemma lnk_app : forall M A B t, lnk M (A ++ B) t <-> lnk M A (hda B t) /\ lnk M B t.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret CB.
      intros M A B t. induction A as [|a A IH]; cbn; [tauto|].
      rewrite hd_app. rewrite IH. destruct A as [|a' A']; (first [solve [clear; cbn; tauto] | cbn; tauto]).
    Qed.

    Lemma last_app_ne : forall {X : Type} (A B : list X) d, B <> [] -> last (A ++ B) d = last B d.
    Proof using.
      intros X A B d HB. induction A as [|a A IH]; [reflexivity|]. cbn. rewrite IH.
      destruct (A ++ B) as [|c C] eqn:HE; [| reflexivity]. apply app_eq_nil in HE. destruct HE as [_ HE]. exfalso. exact (HB HE).
    Qed.

    Lemma lnk_agree : forall M M' Ls t, lnk M Ls t -> (forall a, In a Ls -> agree_on M M' (addr a) 8) ->
      (forall a, In a Ls -> 0 <= addr a /\ addr a + 8 <= 2 ^ 64) -> lnk M' Ls t.
    Proof using sp.
      intros M M' Ls t. induction Ls as [|a Ls IH]; intros HL HA HR; cbn in *; [exact I|].
      destruct HL as [Hc HL]. split.
      - pose proof (HR a (or_introl eq_refl)). eapply cellw_agree; [exact Hc | apply HA; left; reflexivity | lia | cbn; lia].
      - apply IH; [exact HL | intros b Hb; apply HA; right; exact Hb | intros b Hb; apply HR; right; exact Hb].
    Qed.

    Ltac fin_regs FIN HR' :=
      eapply (FIN _ (or_intror I));
      [ let Q := fresh in rreg HR' 2%bv Q; exact Q
      | let Q := fresh in rreg HR' 3%bv Q; exact Q
      | let Q := fresh in rreg HR' 4%bv Q; exact Q
      | exact (syms_id_sound _ _ _ _ [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl)
      | let Q := fresh in rreg HR' 10%bv Q; exact Q
      | let Q := fresh in rreg HR' 8%bv Q; exact Q
      | let Q := fresh in rreg HR' 9%bv Q; exact Q
      | let Q := fresh in rreg HR' 11%bv Q; first [exact Q | rewrite Q; f_equal; lia]
      | let Q := fresh in rreg HR' 15%bv Q; first [exact Q | rewrite Q; reflexivity | rewrite Q; f_equal; lia]
      | let Q := fresh in rreg HR' 14%bv Q; first [exact Q | rewrite Q; rewrite ?w_remu by lia; f_equal; lia]
      | ].

    Lemma perm_nodup : forall A1 M1 Ls, umapx MI 24 (nval24 SEGS) A1 M1 obj bl bc ents -> Permutation Ls ents -> List.NoDup (map addr Ls).
    Proof using AC L MI obj bl bc ents.
      intros A1 M1 Ls U HP. eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact HP|].
      apply base.NoDup_ListNoDup. exact (u_nodup U).
    Qed.

    Lemma nodup_app_ne : forall (l1 l2 : list lent) b b',
      List.NoDup (map addr (l1 ++ l2)) -> In b l1 -> In b' l2 -> addr b <> addr b'.
    Proof using.
      intros l1 l2 b b' Hnd H1 H2 Heq.
      revert Hnd H1. induction l1 as [|x l1 IH]; intros Hnd H1; [destruct H1|].
      cbn in Hnd. inversion Hnd as [|y l Hni Hnd']. subst.
      destruct H1 as [<-|H1].
      - apply Hni. rewrite Heq, map_app. apply in_app_iff. right. apply in_map. exact H2.
      - exact (IH Hnd' H1).
    Qed.

    Lemma last_in : forall (P : list lent) d, P <> [] -> In (last P d) P.
    Proof using.
      intros P d HP. destruct P as [|q P']; [exfalso; exact (HP eq_refl)|].
      assert (Hc : q :: P' <> []) by discriminate. rewrite (app_removelast_last d Hc) at 2. apply in_app_iff. right. left. reflexivity.
    Qed.

    Lemma apart_sub : forall a k b m a' k' b' m', apart a k b m -> a <= a' -> a' + k' <= a + k -> b <= b' -> b' + m' <= b + m -> apart a' k' b' m'.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret CB. unfold apart. intros. lia. Qed.
    Lemma apart_sym : forall a k b m, apart a k b m -> apart b m a k.
    Proof using sp. unfold apart. intros. lia. Qed.

    Lemma splice_facts : forall A1 M1 P S' B x M,
      umapx MI 24 (nval24 SEGS) A1 M1 obj bl bc ents ->
      Permutation (P ++ x :: S') ents -> binv Z n snt P B -> P <> [] ->
      cell8 SEGS M snt (hdaddr (P ++ x :: S')) -> chain SEGS M (P ++ x :: S') ->
      0 <= hh x < n -> B (hh x) <> 0 ->
      exists nt P',
        cell8 SEGS M (B (hh x)) nt /\ 0 <= nt < 2 ^ 64 /\
        (B (hh x) = snt \/ exists y, In y P /\ B (hh x) = addr y /\ addr y <> addr (last P d0) /\ addr y <> addr x) /\
        last P' d0 = last P d0 /\ P' <> [] /\ Permutation (P' ++ S') (P ++ x :: S') /\ binv Z n snt P' B /\
        (forall M3, cell8 SEGS M3 (B (hh x)) (addr x) -> cell8 SEGS M3 (addr x) nt -> cell8 SEGS M3 (addr (last P d0)) (hdaddr S') ->
           (forall a, In a (P ++ S') -> addr a <> addr (last P d0) -> addr a <> addr x -> addr a <> B (hh x) -> agree_on M M3 (addr a) 8) ->
           (B (hh x) <> snt -> agree_on M M3 snt 8) ->
           cell8 SEGS M3 snt (hdaddr (P' ++ S')) /\ chain SEGS M3 (P' ++ S')).
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret obj bl bc ents CB.
      intros A1 M1 P S' B x M U1 PERM BI HP Cp1 CH Hh Hfull.
      pose proof (perm_nodup _ _ _ U1 PERM) as NDL.
      pose proof (u_obj_lo U1) as Hobj0.
      assert (Hnoty : forall e, In e (P ++ x :: S') -> addr e <> snt).
      { intros e He. assert (Hin : In e ents) by (eapply Permutation_in; [exact PERM | exact He]).
        destruct e as [q [k v]]. destruct (u_node U1 q k v Hin) as (_ & Hq0 & _ & _ & _ & _ & _ & _ & Hap & _). unfold apart in Hap. cbn. lia. }
      assert (Hrng : forall e, In e (P ++ x :: S') -> 0 <= addr e /\ addr e + 8 <= 2 ^ 64).
      { intros e He. destruct (ent_facts _ _ e U1 ltac:(eapply Permutation_in; [exact PERM | exact He])) as (H0 & H1 & _). lia. }
      apply lnk_chain in CH.
      set (w := last P d0).
      assert (HwP : In w P) by (unfold w; apply last_in; exact HP).

      pose proof NDL as NDxS. rewrite map_app in NDxS. apply NoDup_app_remove_l in NDxS. cbn in NDxS. apply NoDup_cons_iff in NDxS. destruct NDxS as [HxS NDS].
      assert (HSx : forall a, In a S' -> addr a <> addr x) by (intros a Ha He; apply HxS; rewrite <- He; apply in_map; exact Ha).
      assert (HPx : forall a, In a P -> addr a <> addr x) by (intros a Ha; exact (nodup_app_ne P (x :: S') a x NDL Ha (or_introl eq_refl))).
      assert (HPS : forall a b, In a P -> In b S' -> addr a <> addr b) by (intros a b Ha Hb; exact (nodup_app_ne P (x :: S') a b NDL Ha (or_intror Hb))).
      destruct (bi_just _ _ _ _ _ BI (hh x) Hh Hfull) as [[Ht (x0 & P0 & HP0 & Hx0)] | (P1 & y & z & P2 & HPd & Ht & Hz)].
      -
        exists (addr x0), (x :: P).
        assert (Hhd : hdaddr (P ++ x :: S') = addr x0) by (rewrite HP0; destruct x0 as [q v]; reflexivity).
        assert (HPR : P = removelast P ++ [w]) by (unfold w; apply app_removelast_last; exact HP).
        pose proof NDL as NDP. rewrite map_app in NDP. apply NoDup_app_remove_r in NDP.
        split; [rewrite Ht, <- Hhd; exact Cp1|].
        split; [pose proof (Hrng x0 ltac:(rewrite HP0; left; reflexivity)); lia|].
        split; [left; exact Ht|].
        split; [unfold w; rewrite HP0; reflexivity|].
        split; [discriminate|].
        split; [cbn [app]; apply Permutation_middle|].
        split.
        { apply (step_front Z n snt P x B BI Hh Ht ltac:(lia)).
          intros Q1 y z Q2 HQ. apply Hnoty. apply in_app_iff. left. rewrite HQ. apply in_app_iff. right. left. reflexivity. }
        intros M3 C3t C3x C3w AG AGs.
        split; [replace (hdaddr ((x :: P) ++ S')) with (addr x) by (destruct x as [q v]; reflexivity); rewrite <- Ht; exact C3t|].
        apply lnk_chain. cbn [app lnk]. split; [rewrite hd_app; rewrite HP0; cbn; exact C3x|].
        rewrite HPR in CH |- *. rewrite <- app_assoc in CH |- *. cbn [app] in CH |- *.
        apply lnk_app in CH. destruct CH as [CHR [CHw [CHx CHS]]]. cbn [hda] in CHR.
        apply lnk_app. cbn [lnk hda]. split; [|split; [rewrite <- hdaddr_hda; exact C3w | ]].
        + eapply lnk_agree; [exact CHR | | intros a Ha; apply Hrng; apply in_app_iff; left; rewrite HPR; apply in_app_iff; left; exact Ha].
          intros a Ha. assert (HaP : In a P) by (rewrite HPR; apply in_app_iff; left; exact Ha).
          apply AG; [apply in_app_iff; left; exact HaP | | exact (HPx a HaP) | rewrite Ht; apply Hnoty; apply in_app_iff; left; exact HaP].
          rewrite HPR in NDP. exact (nodup_app_ne _ _ a w NDP Ha (or_introl eq_refl)).
        + eapply lnk_agree; [exact CHS | | intros a Ha; apply Hrng; apply in_app_iff; right; right; exact Ha].
          intros a Ha. apply AG; [apply in_app_iff; right; exact Ha | exact (not_eq_sym (HPS w a HwP Ha)) | exact (HSx a Ha) | rewrite Ht; apply Hnoty; apply in_app_iff; right; right; exact Ha].
      -
        remember (z :: P2) as Q2 eqn:HQ2.
        assert (HQne : Q2 <> []) by (rewrite HQ2; discriminate).
        assert (HhQ : forall u, hda Q2 u = addr z) by (intros u; rewrite HQ2; reflexivity).
        assert (HwQ : last Q2 d0 = w) by (unfold w; rewrite HPd; symmetry; rewrite last_app_ne by discriminate; cbn; rewrite HQ2; reflexivity).
        assert (HQR : Q2 = removelast Q2 ++ [w]) by (rewrite <- HwQ; apply app_removelast_last; exact HQne).
        assert (HwQ2 : In w Q2) by (rewrite HQR; apply in_app_iff; right; left; reflexivity).
        assert (HF1 : P ++ x :: S' = P1 ++ (y :: Q2 ++ x :: S')) by (rewrite HPd, <- app_assoc; reflexivity).
        assert (HF2 : P ++ x :: S' = (P1 ++ [y]) ++ (Q2 ++ x :: S')) by (rewrite HPd, <- !app_assoc; reflexivity).
        assert (HyP : In y P) by (rewrite HPd; apply in_app_iff; right; left; reflexivity).
        assert (HQP : forall a, In a Q2 -> In a P) by (intros a Ha; rewrite HPd; apply in_app_iff; right; right; exact Ha).
        pose proof NDL as ND2. rewrite HF2 in ND2.
        assert (HyQS : forall a, In a (Q2 ++ x :: S') -> addr y <> addr a) by (intros a Ha; exact (nodup_app_ne _ _ y a ND2 ltac:(apply in_app_iff; right; left; reflexivity) Ha)).
        rewrite map_app in ND2. apply NoDup_app_remove_l in ND2.
        pose proof ND2 as NDQ. rewrite map_app in NDQ. apply NoDup_app_remove_r in NDQ. rewrite HQR in NDQ.
        pose proof NDL as ND1. rewrite HF1 in ND1.
        assert (Hyw : addr y <> addr w) by (apply HyQS; apply in_app_iff; left; exact HwQ2).
        exists (addr z), (P1 ++ y :: x :: Q2).
        rewrite HF1 in CH. apply lnk_app in CH. destruct CH as [CH1 CH2]. cbn [lnk hda] in CH1, CH2. destruct CH2 as [Cy CH3].
        rewrite hd_app, HhQ in Cy.
        apply lnk_app in CH3. destruct CH3 as [CHQ [CHx CHS]]. cbn [hda] in CHQ.
        rewrite HQR in CHQ. apply lnk_app in CHQ. destruct CHQ as [CHR [CHw _]]. cbn [hda] in CHR, CHw.
        split; [rewrite Ht; exact Cy|].
        split; [pose proof (Hrng z ltac:(rewrite HF1; apply in_app_iff; right; right; apply in_app_iff; left; rewrite HQ2; left; reflexivity)); lia|].
        split; [right; exists y; split; [exact HyP | split; [exact Ht | split; [exact Hyw | apply HyQS; apply in_app_iff; right; left; reflexivity]]]|].
        split; [rewrite last_app_ne by discriminate; cbn; rewrite <- HwQ; destruct Q2; [exfalso; exact (HQne eq_refl) | reflexivity]|].
        split; [destruct P1; discriminate|].
        split; [rewrite HF1, <- app_assoc; cbn [app]; apply Permutation_app_head; apply perm_skip; apply Permutation_middle|].
        split.
        { rewrite HQ2. apply step_splice; [rewrite <- HQ2, <- HPd; exact BI | exact Ht | rewrite Hz; reflexivity | apply Hnoty; apply in_app_iff; left; exact HyP
          | pose proof (Hnoty y ltac:(apply in_app_iff; left; exact HyP)); destruct (ent_facts _ _ y U1 ltac:(eapply Permutation_in; [exact PERM | apply in_app_iff; left; exact HyP])) as (Hy0 & _); lia
          | pose proof NDL as NDP; rewrite map_app in NDP; apply NoDup_app_remove_r in NDP; rewrite HPd, HQ2 in NDP; exact NDP]. }
        intros M3 C3t C3x C3w AG AGs.
        assert (Hts : B (hh x) <> snt) by (rewrite Ht; apply Hnoty; apply in_app_iff; left; exact HyP).
        split.
        { rewrite hdaddr_hda, <- app_assoc, hd_app. cbn [hda]. rewrite hdaddr_hda, HF1, hd_app in Cp1. cbn [hda] in Cp1.
          pose proof (u_obj_hi U1). eapply cellw_agree; [exact Cp1 | exact (AGs Hts) | lia | cbn; lia]. }
        apply lnk_chain. rewrite <- app_assoc. cbn [app]. apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- Ht; exact C3t | split; [rewrite hd_app, HhQ; exact C3x |]]].
        + eapply lnk_agree; [exact CH1 | | intros a Ha; apply Hrng; rewrite HF1; apply in_app_iff; left; exact Ha].
          intros a Ha. assert (HaP : In a P) by (rewrite HPd; apply in_app_iff; left; exact Ha).
          apply AG; [apply in_app_iff; left; exact HaP | | exact (HPx a HaP) | rewrite Ht].
          * exact (nodup_app_ne _ _ a w ND1 Ha ltac:(right; apply in_app_iff; left; exact HwQ2)).
          * exact (nodup_app_ne _ _ a y ND1 Ha (or_introl eq_refl)).
        + apply lnk_app. split.
          * rewrite HQR. apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- hdaddr_hda; exact C3w | exact I]].
            eapply lnk_agree; [exact CHR | | intros a Ha; apply Hrng; apply in_app_iff; left; apply HQP; rewrite HQR; apply in_app_iff; left; exact Ha].
            intros a Ha. assert (HaQ : In a Q2) by (rewrite HQR; apply in_app_iff; left; exact Ha).
            apply AG; [apply in_app_iff; left; exact (HQP a HaQ) | exact (nodup_app_ne _ _ a w NDQ Ha (or_introl eq_refl)) | exact (HPx a (HQP a HaQ)) | rewrite Ht; exact (not_eq_sym (HyQS a ltac:(apply in_app_iff; left; exact HaQ)))].
          * eapply lnk_agree; [exact CHS | | intros a Ha; apply Hrng; apply in_app_iff; right; right; exact Ha].
            intros a Ha. apply AG; [apply in_app_iff; right; exact Ha | exact (not_eq_sym (HPS w a HwP Ha)) | exact (HSx a Ha) | rewrite Ht; exact (not_eq_sym (HyQS a ltac:(apply in_app_iff; right; right; exact Ha)))].
    Qed.

    Lemma nodes_apart : forall A1 M1 a b, umapx MI 24 (nval24 SEGS) A1 M1 obj bl bc ents -> In a ents -> In b ents -> addr a <> addr b ->
      apart (addr a) 24 (addr b) 24.
    Proof using AC L MI obj bl bc ents.
      intros A1 M1 a b U Ha Hb Hne. apply (u_napart U); [apply in_map; exact Ha | apply in_map; exact Hb | exact Hne].
    Qed.

    Lemma p_node_apart : forall p A M model e, ainv MI A M model -> In (p, 8 * n) (live MI A) -> ~ In p (map fst (live MI A0)) ->
      In (addr e, 24) (live MI A) -> In e ents -> apart p (8 * n) (addr e) 24.
    Proof using AC L MI A0 M0 obj bl bc ents U0.
      intros p A M model e AI Hp Hpnew He Hin.
      apply (ai_live_disjoint MI A M model p (8 * n) (addr e) 24 AI Hp He). intros Heq. apply Hpnew. rewrite Heq.
      apply (in_map fst _ (addr e, 24)). destruct e as [q [k v]]. exact (proj1 (u_node U0 q k v Hin)).
    Qed.

Ltac fin_regs2 FIN HR' :=
      eapply (FIN _ _ eq_refl);
      [ let Q := fresh in rreg HR' 2%bv Q; exact Q
      | let Q := fresh in rreg HR' 3%bv Q; exact Q
      | let Q := fresh in rreg HR' 4%bv Q; exact Q
      | exact (syms_id_sound _ _ _ _ [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl)
      | let Q := fresh in rreg HR' 10%bv Q; exact Q
      | let Q := fresh in rreg HR' 8%bv Q; exact Q
      | let Q := fresh in rreg HR' 9%bv Q; exact Q
      | let Q := fresh in rreg HR' 11%bv Q; first [exact Q | rewrite Q; f_equal; lia]
      | let Q := fresh in rreg HR' 15%bv Q; first [exact Q | rewrite Q; reflexivity | rewrite Q; f_equal; lia]
      | let Q := fresh in rreg HR' 14%bv Q; first [exact Q | rewrite Q; rewrite ?w_remu by lia; f_equal; lia]
      | ].

    Ltac sub_of x y := lazymatch y with | x => idtac | Z.add x _ => idtac | Z.add (Z.add x _) _ => idtac end.
    Ltac dj_apart Hr :=
      cbn [a_off]; rewrite ?Z.add_0_r;
      lazymatch goal with |- ?a + ?k <= ?b \/ ?b + ?m <= ?a => change (apart a k b m) end;
      match goal with H : apart ?a0 _ ?b0 _ |- apart ?a _ ?b _ =>
        first [ sub_of a0 a; sub_of b0 b; eapply (apart_sub _ _ _ _ _ _ _ _ H); clear - Hr; lia
              | sub_of a0 b; sub_of b0 a; eapply (apart_sub _ _ _ _ _ _ _ _ (apart_sym _ _ _ _ H)); clear - Hr; lia ] end.
    Ltac dj Hh := eapply sc_disjZ;
      [ evs; rewrite ?w_remu, ?w_mul, ?w_add by lia; rewrite ?v_addi_Z by lia; rewrite ?Hh; reflexivity
      | evs; rewrite ?w_remu, ?w_mul, ?w_add by lia; rewrite ?v_addi_Z by lia; rewrite ?Hh; reflexivity
      | lia | lia | lia | lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; unfold apart in *; lia ].

    Ltac nrm Hrm Hba := rewrite ?Hrm; rewrite ?Hba.
    Ltac rdq Hrm Hba H :=
      lazymatch type of H with cellw _ _ ?a _ _ =>
      eapply (sc_read_cellw _ _ _ _ _ _ _ _ H);
      [ apply N.le_refl
      | evs; nrm Hrm Hba; lazymatch goal with |- v_addi (Z_to_bv 64 ?b) _ = _ => sub_of b a end;
        rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r; reflexivity
      | evs; reflexivity ] end.
    Ltac djq Hrm Hba Hr := eapply sc_disjZ;
      [ evs; nrm Hrm Hba; reflexivity | evs; nrm Hrm Hba; reflexivity
      | lia | lia | lia | lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | dj_apart Hr ].
    Ltac soq Hrm Hba := eapply (sc_storeok _ _ _ _ _ 8);
      [ evs; nrm Hrm Hba; reflexivity | lia | cbn [a_off]; lia | cbn [a_off]; lia
      | cbn [a_off]; rewrite ?Z.add_0_r;
        first [ lazymatch goal with |- defined _ ?a _ => match goal with D : defined _ a _ |- _ => eapply (defined_sub _ _ _ _ _ D); lia end end
              | match goal with D : defined _ _ _ |- _ => eapply (defined_sub _ _ _ _ _ D); lia end ] ].
    Ltac flq Hrm Hba := eapply sc_flat; [evs; nrm Hrm Hba; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia].
    Ltac brq Hrm Hba := cbn [sc_denot]; evs; nrm Hrm Hba; rewrite ?br_eq, ?br_ne, ?br_ltu by lia; bool_lia.

    Ltac trapq Hrm Hba :=
      first [ eapply sc_trap_align; [evs; nrm Hrm Hba; reflexivity | lia | first [assumption | apply align16_8; assumption] ]
            | eapply sc_trap_srl; [evs; nrm Hrm Hba; rewrite ?w_add by lia; reflexivity | lia | lia]
            | eapply sc_trap_null; [evs; nrm Hrm Hba; reflexivity | lia]
            | eapply sc_trap_wrap; [evs; nrm Hrm Hba; reflexivity | evs; reflexivity | lia | lia | lia] ].

    Ltac popq := cbn [sc_denot]; evs; rewrite branch_ltu_lit_l by lia; bool_lia.
    Ltac scq Hrm Hba Hr :=
      lazymatch goal with
      | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_AND _ (ELit 7)) (ELit 0)) => trapq Hrm Hba
      | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_SRL _ (ELit 61)) (ELit 0)) => trapq Hrm Hba
      | |- sc_denot _ _ _ (SCBr true BC_LTU (ELit 1) _) => popq
      | |- sc_denot _ _ _ (SCBr _ _ _ _) => first [brq Hrm Hba | trapq Hrm Hba]
      | |- sc_denot _ _ _ (SCFlat _ _) => flq Hrm Hba
      | |- sc_denot _ _ _ (SCDisj _ _ _ _) => djq Hrm Hba Hr
      | |- sc_denot _ _ _ (SCStoreOk _ _) => soq Hrm Hba
      | |- sc_denot _ _ _ (SCReadBase _ _ _ _) => match goal with H : cellw _ _ _ 8%N _ |- _ => rdq Hrm Hba H end
      end.
    Ltac scqs Hrm Hba Hr := split_scs; scq Hrm Hba Hr.

    Ltac finq Hrm Hba FIN HR' :=
      eapply FIN;
      [ first [ exact (or_intror I) | evs; nrm Hrm Hba; rewrite ?w_add, ?v_addi_Z by lia; rewrite ?Z.add_0_r; reflexivity ]
      | let Q := fresh in rreg HR' 2%bv Q; exact Q
      | let Q := fresh in rreg HR' 3%bv Q; exact Q
      | let Q := fresh in rreg HR' 4%bv Q; exact Q
      | exact (syms_id_sound _ _ _ _ [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl)
      | let Q := fresh in rreg HR' 10%bv Q; exact Q
      | let Q := fresh in rreg HR' 8%bv Q; exact Q
      | let Q := fresh in rreg HR' 9%bv Q; first [exact Q | rewrite Q; rewrite ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]
      | let Q := fresh in rreg HR' 11%bv Q; exact Q
      | let Q := fresh in rreg HR' 15%bv Q; rewrite Q; reflexivity
      | let Q := fresh in rreg HR' 14%bv Q; rewrite Q; nrm Hrm Hba; first [reflexivity | f_equal; lia]
      | let Q := fresh in rreg HR' 12%bv Q; exact Q
      | let Q := fresh in rreg HR' 13%bv Q; exact Q
      | let Q := fresh in rreg HR' 16%bv Q; exact Q
      | let Q := fresh in rreg HR' 17%bv Q; exact Q
      | ].
  End Main.
End Reh.
