(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, lemmas added for the revision. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import GapGrid.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require LazyNodes.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel LazyRestrict LazyLedger LazySR Gap04.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsDepotInv SecGap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc2eq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AllocRepX3HCW~~~~~~j54AHSB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~nf6AHI_LOnf2shnf5aceil46Stdlib6ZArith6BinInt1Zt32lehc3andt32lt04Npos35stdpp9bitvectorbdefinitionshg12bv37Corelib4Init9Datatypeshi44boolhi44prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~hkc3ehit33ltbhi44list69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hpd4zlenj55ehigh36Stdlib5Lists4Listhue6filterhi43snd37Corelib5Lists7ListDefih23map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6SecGap~~~~~~ij04zsumhg1bbv_unsignedhpd6schunkhpdasc_map_beghpdbsc_map_sizet33addhpd6astatehpd6as_secj56schight33powj54hcnthi44consj54hlenhi43appih26Forall3h5LinuxProcessSemanticsfLinuxProcessSem5Stateivaamap_removehi43fsthue2Int33subhi43nilj54hsec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~jl72wzhi44pairhpd4mkSCnf3memhi44Nonehi46optionhi44truehc3not3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjse5wview79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~kge5asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~kl23a_S69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~kp7ain_rangesb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ku44cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~li88rw_cellsku42C8hc2exkl27ACFLAGSj59ASSPGUARDku42C1j58AGOT_SSPj59ALIBCPGSZjl72b8iva5Modeliva7vm_mapshc2orkl24a_pakge8AIMG_TOPivacmap_containskl24a_Zrkl24a_sbnf9ALOWSH_LOhi45falseivabvm_noaccesshpd9kPageSizehpdh0kPtrArrayReserveivabvm_reservedhpdakSpaceSizekl22RBkl23a_Lkl25a_ctxkl25a_fsbkl25a_thriva6VmMapsiva9alloc_topiva8m_vmmapsivabregion_freeivah2target_alloc_limitiva8vm_limithpdbkNumClasseshpdbkRegionSizekge7AIMG_LOkl28AFS_SIZEj54AHC0j54AHL0j57ASECMAX69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~nie5hceilkl26AMODEL99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AllocRepX3HCW1X~~~~~~nnc7akernelkp7h5same_but_materializednnc7AMODELXnnc8awin_vis79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~nvd5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv~~~~~~ok25depotok24d_nbok24d_sbt33mulj59depot_covij04costkl24a_stkl23astj54AGAPj57akernel" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ALIBCPGSZ : Z := 0x7115d8.   (* [comment removed for export] *)
Definition AGOT_SSP  : Z := 0x1b3108.   (* [comment removed for export] *)
Definition ASSPGUARD : Z := 0x711358.   (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AHSB : Z := 0x2008fff7000.
Lemma AHSB_eq : ltac2:(zQ "50!j0!h9!n8!rd!s6@3$0$1$2@1$4$3").
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sh_ceiling_range : ltac2:(zQ "40!sb!s6!ub!v0@2$3@2$2+hgggmvuvogg0@1$1@1$0?5HCEIL@2$2@1$1@1$0?5HCEIL+hgggnvuvogg0").
Proof. acb. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.
Lemma sh_ceiling_lt_AHI_LO : ltac2:(zQ "40!rd!sb!s6!v6@2$3@1$2@1$1?5HCEIL$0").
Proof. pose proof sh_ceiling_range. unfold AHI_LO. lia. Qed.

(* LPS 727298f3: the floor of the launch's vDSO/vvar pair, which [State.init_model] adds to the
   reserved ledger below [vdso_top].  [vdso_top] is the page below [min mmap_base alloc_top]; the
   main phase has [mmap_base_min <= vm_mmap_base] ([AsanPlanSound.co_res]) and [alloc_top = hceil]
   far above it, and the pair is at most 20 pages ([State.vdso_len_bounds]), so its base is at least
   0x154555543000.  This is that, rounded down; it lies far above [AHI_LO]. *)
Definition ARESX_LO : Z := 0x154555000000.

(* [comment removed for export] *)
Definition ehigh : ltac2:(zQ "40!vb!hhe!hjc!hk4>1e@2$3@1$1@1$0#k0@1$1@1$0#k0$2") := ltac2:(zQ "60!vb!hhe!hk4!rd!ho8!hof\1e@2$2@1$1@1$0#k0@1$1@1$0#k0@2$5$3@1$4^1").      (* [comment removed for export] *)
Definition hcnt : ltac2:(zQ "50!vb!hhe!hp5!hk4!h9>1E@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0$4") := ltac2:(zQ "71!vb!hhe!hk4!hp5!hte!hu6!ig1&@2$2@1$1@1$0#k0@1$1@1$0#k0\1E@1$3~0@2$4~0@3$6~0$5^1").
Definition hlen : ltac2:(zQ "50!vb!hhe!hp5!hk4!h9>1E@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0$4") := ltac2:(zQ "b1!vb!hhe!hk4!hp5!igb!ii9!h9!hu6!imc!ig1!in4&@2$2@1$1@1$0#k0@1$1@1$0#k0\1E@1$3~0@1$8@4$5~0$6\1e~0@2$a@1$0#k0@3$4@1$1@1$0#k0@1$1@1$0#k0^1@3$9~0$7^1").
Definition schigh : ltac2:(zQ "20!hjc!io3>2sc$1$0") := ltac2:(zQ "60!iod!ipb!io3!rd!iqa!hof\2sc$2@2$5$3@2$4@1$0^1@1$1^1").
Definition hsec : ltac2:(zQ "30!hp5!ir0!io3>2st$1@1$0$2") := ltac2:(zQ "50!ira!ir0!io3!is4!ig1\2st$1@3$4$2$3@1$0^1").
Definition AHC0 : Z := 32.            (* [comment removed for export] *)
Definition AHL0 : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!isd@2$0+2+i6").        (* [comment removed for export] *)
Definition ASECMAX : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!isd!iqa@2$1@2$0+2+i0@2$0+2+e").   (* [comment removed for export] *)

Lemma hcnt_nil : hcnt [] = 0. Proof. reflexivity. Qed.
Lemma hlen_nil : hlen [] = 0. Proof. reflexivity. Qed.
Lemma hcnt_cons : ltac2:(zQ "b1!vb!hhe!hk4!hjc!h9!it3!ita!hp5!j0!hu6!iqa&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>1E@1$7~0@3$8$4@1$5@3$6~0^2^1@2$aM3\0$3$4@1$9^2+1Z@1$5^1").
Proof. intros e E. unfold hcnt, zlen. cbn [List.filter]. destruct (ehigh e); cbn [length]; lia. Qed.
Lemma hlen_cons : ltac2:(zQ "d1!vb!hhe!hk4!hjc!h9!iu2!ita!hp5!igb!j0!hu6!iqa!in4&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>1E@1$7~0@3$9$4@1$5@3$6~0^2^1@2$bM3\0$3$4@1$a^2@2$c@1$0#k0@3$8@1$1@1$0#k0@1$1@1$0#k0^2Z@1$5^1").
Proof. intros e E. unfold hlen. cbn [List.filter]. destruct (ehigh e); cbn [map zsum]; lia. Qed.
Lemma hcnt_nonneg : ltac2:(zQ "60!vb!hhe!hp5!hk4!it3!ub>1E@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0@2$5Z@1$4^1"). Proof. intros E. unfold hcnt, zlen. lia. Qed.
Lemma hlen_nonneg : ltac2:(zQ "60!vb!hhe!hp5!hk4!iu2!ub>1E@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0@2$5Z@1$4^1").
Proof. intros E. induction E as [|e E IH]; [rewrite hlen_nil; lia|]. rewrite hlen_cons. pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia. Qed.
Lemma hcnt_cons_ge : ltac2:(zQ "71!vb!hhe!hk4!it3!ita!hp5!ub&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>1E@1$5~0@2$6@1$3^1@1$3@3$4~0^2^1").
Proof. intros e E. rewrite hcnt_cons. destruct (ehigh e); lia. Qed.
Lemma hlen_cons_ge : ltac2:(zQ "71!vb!hhe!hk4!iu2!ita!hp5!ub&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>1E@1$5~0@2$6@1$3^1@1$3@3$4~0^2^1").
Proof. intros e E. rewrite hlen_cons. pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia. Qed.
Lemma hcnt_app : ltac2:(zQ "92!vb!hhe!hk4!it3!hp5!iu9!j0!h9!iqa&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2E1~1>2E2~1@3$6$7@1$3@3$5~0^2^1@2$8@1$3^2@1$3^1").
Proof. intros E1 E2. unfold hcnt, zlen. rewrite filter_app, length_app. lia. Qed.
Lemma hlen_app : ltac2:(zQ "92!vb!hhe!hk4!iu2!hp5!iu9!j0!h9!iqa&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2E1~1>2E2~1@3$6$7@1$3@3$5~0^2^1@2$8@1$3^2@1$3^1").
Proof. intros E1 E2. unfold hlen. rewrite filter_app, map_app, zsum_app. reflexivity. Qed.
Lemma hcnt_low_cons : ltac2:(zQ "b1!vb!hhe!hk4!it3!ita!hp5!j0!h9!rd!ho8!ub&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>1E@1$5~0>0@2$a@1$9^2$8@3$6$7@1$3@3$4~0^3^2@1$3^2").
Proof. intros e E H. rewrite hcnt_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hlen_low_cons : ltac2:(zQ "b1!vb!hhe!hk4!iu2!ita!hp5!j0!h9!rd!ho8!ub&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>1E@1$5~0>0@2$a@1$9^2$8@3$6$7@1$3@3$4~0^3^2@1$3^2").
Proof. intros e E H. rewrite hlen_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hcnt_high_cons : ltac2:(zQ "c1!vb!hhe!hk4!it3!ita!hp5!j0!h9!rd!ho8!iqa!v6&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>1E@1$5~0>0@2$b$8@1$9^2@3$6$7@1$3@3$4~0^3^2@2$a+1@1$3^2").
Proof. intros e E H. rewrite hcnt_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hlen_high_cons : ltac2:(zQ "e1!vb!hhe!hk4!iu2!ita!hp5!igb!j0!h9!rd!ho8!iqa!v6!in4&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>1E@1$5~0>0@2$c$9@1$a^2@3$7$8@1$3@3$4~0^3^2@2$b@2$d@1$0#k0@3$6@1$1@1$0#k0@1$1@1$0#k0^3@1$3^2").
Proof. intros e E H. rewrite hlen_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hcnt_low : ltac2:(zQ "b1!vb!hhe!hk4!hp5!j0!iv0!h9!it3!rd!ho8!ub&@2$2@1$1@1$0#k0@1$1@1$0#k0>1E@1$3~0>0@3$5~0\1e~0@2$a@1$9^1$8^1@3$4$6@1$7^2Z").
Proof. intros E H. induction H as [|e E He H IH]; [reflexivity|]. rewrite hcnt_low_cons by exact He. exact IH. Qed.
Lemma hlen_low : ltac2:(zQ "b1!vb!hhe!hk4!hp5!j0!iv0!h9!iu2!rd!ho8!ub&@2$2@1$1@1$0#k0@1$1@1$0#k0>1E@1$3~0>0@3$5~0\1e~0@2$a@1$9^1$8^1@3$4$6@1$7^2Z").
Proof. intros E H. induction H as [|e E He H IH]; [reflexivity|]. rewrite hlen_low_cons by exact He. exact IH. Qed.
Lemma hcnt_le_len : ltac2:(zQ "71!vb!hhe!hk4!hp5!hte!it3!ub&@2$2@1$1@1$0#k0@1$1@1$0#k0>1E@1$3~0@2$6@1$5^1@2$4~0^1").
Proof. intros E. induction E as [|e E IH]; [rewrite hcnt_nil; unfold zlen; cbn; lia|]. rewrite hcnt_cons. unfold zlen in *. cbn [length]. destruct (ehigh e); lia. Qed.
Lemma hlen_le_total : ltac2:(zQ "b1!vb!hhe!hk4!hp5!igb!ii9!h9!iu2!imc!ub!in4&@2$2@1$1@1$0#k0@1$1@1$0#k0>1E@1$3~0@2$9@1$7^1@1$8@4$5~0$6\1e~0@2$a@1$0#k0@3$4@1$1@1$0#k0@1$1@1$0#k0^1^1").
Proof.
  intros E. induction E as [|e E IH]; [rewrite hlen_nil; cbn; lia|]. rewrite hlen_cons. cbn [map zsum].
  pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia.
Qed.
(* [comment removed for export] *)
Lemma hcnt_map_remove_le : ltac2:(zQ "70!vb!hhe!it3!hp5!hk4!ji8!ub>1E@1$3@2$4@1$1@1$0#k0@1$1@1$0#k0>2lo@1$1@1$0#k0@2$6@1$2@2$5^2^1@1$2^2").
Proof.
  intros E lo. unfold map_remove. induction E as [|e E IH]; [cbn; lia|]. cbn [List.filter].
  destruct (negb (bv_eqb (fst e) lo)); [rewrite !hcnt_cons; destruct (ehigh e); lia| pose proof (hcnt_cons_ge e E); lia].
Qed.
Lemma hlen_map_remove_le : ltac2:(zQ "70!vb!hhe!iu2!hp5!hk4!ji8!ub>1E@1$3@2$4@1$1@1$0#k0@1$1@1$0#k0>2lo@1$1@1$0#k0@2$6@1$2@2$5^2^1@1$2^2").
Proof.
  intros E lo. unfold map_remove. induction E as [|e E IH]; [cbn; lia|]. cbn [List.filter].
  destruct (negb (bv_eqb (fst e) lo)); [rewrite !hlen_cons; destruct (ehigh e); lia| pose proof (hlen_cons_ge e E); lia].
Qed.
Lemma hcnt_map_remove_in : ltac2:(zQ "d1!vb!hhe!hk4!it3!jj6!hp5!ji8!rd!ho8!jjd!ub!v6!jk3&@2$2@1$1@1$0#k0@1$1@1$0#k0>1E@1$5~0>1e~0>0@3$9~0^1^2>0@2$b$7@1$8^2@2$a@1$3@2$6^4@3$4@1$1@1$0#k0@1$1@1$0#k0^3@2$c@1$3^4+1").
Proof.
  intros E e IN H. unfold map_remove. induction E as [|e0 E IH]; [destruct IN|]. cbn [List.filter].
  destruct IN as [->|IN].
  - rewrite bv_eqb_refl. cbn [negb]. rewrite (hcnt_high_cons e E H). pose proof (hcnt_map_remove_le E (fst e)) as L. unfold map_remove in L. lia.
  - specialize (IH IN). destruct (negb (bv_eqb (fst e0) (fst e))); [rewrite !hcnt_cons; destruct (ehigh e0); lia| pose proof (hcnt_cons_ge e0 E); lia].
Qed.
Lemma hlen_map_remove_in : ltac2:(zQ "f1!vb!hhe!hk4!iu2!jj6!hp5!igb!ji8!rd!ho8!jjd!ub!v6!jk3!in4&@2$2@1$1@1$0#k0@1$1@1$0#k0>1E@1$5~0>1e~0>0@3$a~0^1^2>0@2$c$8@1$9^2@2$b@1$3@2$7^4@3$4@1$1@1$0#k0@1$1@1$0#k0^3@2$d@1$3^4@2$e@1$0#k0@3$6@1$1@1$0#k0@1$1@1$0#k0^3").
Proof.
  intros E e IN H. unfold map_remove. induction E as [|e0 E IH]; [destruct IN|]. cbn [List.filter].
  destruct IN as [->|IN].
  - rewrite bv_eqb_refl. cbn [negb]. rewrite (hlen_high_cons e E H). pose proof (hlen_map_remove_le E (fst e)) as L. unfold map_remove in L. lia.
  - specialize (IH IN). destruct (negb (bv_eqb (fst e0) (fst e))); [rewrite !hlen_cons; destruct (ehigh e0); lia| pose proof (hlen_cons_ge e0 E); lia].
Qed.
(* [comment removed for export] *)
Lemma hsec_nil_st : ltac2:(zQ "70!io3!hp5!jk9!j0!ira!ir0!jl0>2st$5>0@3$3@1$1$0@1$4^1@1$2$0@3$3@1$1$0@1$6^2@1$2$0").
Proof. intros st E. unfold hsec. rewrite E. reflexivity. Qed.
Lemma zlen_filter_app {A} : forall (f : A -> bool) l1 l2, zlen (List.filter f (l1 ++ l2)) = zlen (List.filter f l1) + zlen (List.filter f l2).
Proof. intros f l1 l2. unfold zlen. rewrite filter_app, length_app. lia. Qed.
Lemma zsum_size_filter_app : ltac2:(zQ "b0!io3!h9!ii9!ipb!imc!ig1!hp5!iu9!hjc!j0!iqa>1f>0$0$8>2l1@1$6$0>2l2@1$6$0@3$9$1@1$4@4$2$0$1$3@3$5$0^3@3$7$0^2^1@2$a@1$4@4$2$0$1$3@3$5$0^3^2@1$4@4$2$0$1$3@3$5$0^3^1").
Proof. intros f l1 l2. rewrite filter_app, map_app, zsum_app. reflexivity. Qed.
Lemma ehigh_wz : ltac2:(zQ "e1!v0!vb!h9!jp2!ub!v6!isd!hhe!hjc!jp8!j0!jq0!hu6!is4&@2$0@2$4Z^2@2$5^2@2$6+2+k0>1a$2>1n$2>0~0>0~0@3$a$8@1$c@4$9@1$7@1$1#k0@1$7@1$1#k0@1$3^4@1$3^3@1$d@3$b^4^3Z").
Proof. intros a n Ha Hn. unfold ehigh, schigh, KInv.ehi, wz. cbn [fst snd sc_map_beg sc_map_size]. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* LPS 727298f3: mappings apart from a ledger stay apart from it after a cut: every piece
   [maps_subtract] leaves lies inside the entry it came from ([LazyRestrict.iv_subtract_within]).
   Used where a step unmaps part of the mappings and [akernel_resx] must carry over. *)
Lemma apart_maps_subtract : forall (L R : list (word * word)) (lo hi : Z),
  entries_nowrap L -> hi <= 2 ^ 64 ->
  (forall iv, In iv L -> forall e, In e R ->
     bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e)
     \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst iv)) ->
  forall iv, In iv (maps_subtract L lo hi) -> forall e, In e R ->
     bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e)
     \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst iv).
Proof.
  intros L R lo hi NW Hhi HD. unfold entries_nowrap in NW.
  induction L as [|[a sz] L IH]; intros iv Hiv e He; [destruct Hiv|].
  cbn [maps_subtract] in Hiv. apply in_app_or in Hiv as [Hiv|Hiv].
  - destruct iv as [b m].
    assert (NA : bv_unsigned a + bv_unsigned sz <= 2 ^ 64) by exact (NW (a, sz) (or_introl eq_refl)).
    destruct (iv_subtract_within a sz lo hi b m NA Hhi Hiv) as [W1 W2].
    pose proof (HD (a, sz) (or_introl eq_refl) e He) as D. cbn [fst snd] in *. lia.
  - apply IH; [intros x Hx; apply NW; right; exact Hx | intros x Hx; apply HD; right; exact Hx | exact Hiv | exact He].
Qed.

Section X.
  Variable s : ltac2:(zQ "10!ord$0").
  Let st : ltac2:(zQ "10!ir0$0") := ltac2:(zQ "10!or5@1$0?1s").

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition awin_vis : ltac2:(zQ "10!jq8>1m$0P") := ltac2:(zQ "d0!vb!hhe!j0!jqe!hjc!jr6!js0!js8!kg5!kk9!kp0!jq8!kt6\1m$b>1x@1$1@1$0#k0>0@3$2$4@2$c^1@1$a?1s$6@1$7@3$2@1$5@1$1@1$0#8@3$8$9^3^2@1$3@1$1@1$0#8").

  (* [comment removed for export] *)
  Definition flagsx_rep : ltac2:(zQ "10!jq8>1m$0P") := ltac2:(zQ "h30!li0!ita!jk9!kk9!lm3!v0!vb!hhe!lmf!ln5!lna!lo5!lp1!jp2!iqa!lp7!lq2!jq8!lqe\1m$h1@2$5@4$4$3^1$h0@3$1$0@1$8@1$d+hgg0@1$2$0@2$5@4$4$3^1$f@3$1$0@1$8@1$d$b@1$2$0@2$5@2$9@1$7@1$6#k0\1g@1$7@1$6#k0@4$4$3^2$b@3$1$0@1$8^1@1$2$0@2$5@4$4$3^1@2$e$a+tb@3$1$0@1$c@1$h2+1@1$2$0@2$9@1$7@1$6#8\1b@1$7@1$6#8@4$4$3^2@2$e$a+v4@3$1$0@1$c^1@1$2$0").

  (* LPS 727298f3: [akernel] is [akernel_pre /\ akernel_resx].  [akernel_pre] is the former
     eighteen-conjunct invariant, in order, with only the first conjunct's list changed: that
     bound held of [vm_reserved h] when the ledger was the image's reservations alone, and is
     false now that [State.init_model] appends the launch's vDSO/vvar pair, which hangs off
     [mmap_base], not off the image.  The bound keeps its text over the image's reservations,
     and [akernel_resx] carries the pair.  An abbreviation, so that a hypothesis of the old
     conjunction is still syntactically one (as in boost-beast/http_request's port). *)
  #[local] Notation akernel_pre mo :=
    ((let h := m_vmmaps mo in
       (forall e, In e (segments_reserved asegs) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= AIMG_TOP)
    /\ (vm_limit h = target_alloc_limit /\ alloc_top h = hceil)
    /\ (forall x : word,
          (a_thr s <= bv_unsigned x < a_thr s + kPageSize \/ a_ctx s <= bv_unsigned x < a_ctx s + 160
           \/ a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize \/ a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve
           \/ a_fsb s <= bv_unsigned x < a_fsb s + AFS_SIZE
           \/ sh AHI_LO <= bv_unsigned x < AHI_LO) ->
          in_rangesb x (vm_maps h) = true)
    /\ (forall (a n : word) (c : Z), 0 <= c < kNumClasses -> RB s c <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= RB s c + kRegionSize ->
          map_contains (vm_maps h) a n = true)
    /\ (forall a n : word, a_pa s <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= a_pa s + kPtrArrayReserve ->
          map_contains (vm_maps h) a n = true)
    /\ (forall a n : word, sh AHI_LO <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh aceil ->
          map_contains (vm_maps h) a n = true)
    /\ (forall x : word, a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize -> in_rangesb x (a_Zr s) = false)
    /\ (forall x : word, a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve -> in_rangesb x (a_Zr s) = false)
    /\ (forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (a_Zr s) = true /\ in_rangesb x (a_L s) = true)
    /\ (forall x : word, in_rangesb x (vm_noaccess h) = true -> in_rangesb x (vm_maps h) = true)
    /\ (forall sc (x : word), In sc (as_sec st) -> sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc ->
          in_rangesb x (vm_noaccess h) = false)
    /\ (forall sc, In sc (as_sec st) -> In (wz (sc_map_beg sc), wz (sc_map_size sc)) (vm_maps h))
    /\ (forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true)
    /\ (forall a n : word, sh AIMG_TOP <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO ->
          map_contains (vm_maps h) a n = true)
    /\ (forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x (a_Zr s) = true /\ in_rangesb x (a_L s) = true)
    /\ (forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved h) = true)
    /\ (hcnt (vm_maps h) <= AHC0 + zlen (hsec st) /\ hlen (vm_maps h) <= AHL0 + zsum (map sc_map_size (hsec st))
        /\ (forall sc, In sc (as_sec st) -> 0 <= sc_map_size sc <= ASECMAX))
    /\ (forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil)
                           \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
          region_free (vm_noaccess h) a n = true))) (only parsing).

  (* The launch's extra reserved intervals (the vDSO/vvar pair, [AsanPlanSound.co_res]): the
     ledger is the image's reservations followed by them; each is page-aligned, nonempty, above
     the image, above [AHI_LO] (where every window this unit maps ends) and above [ARESX_LO];
     there are at most two, of at most 81920 bytes together ([State.vdso_len_bounds]); and every
     mapping is apart from every reserved interval (the third conjunct of [co_res]), which is
     what frees a range inside a mapping from the ledger ([ak_resf_inside]). *)
  Definition akernel_resx (mo : Model) : Prop :=
    let h := m_vmmaps mo in
    exists rx : list (word * word),
      vm_reserved h = segments_reserved asegs ++ rx
      /\ (forall e, In e rx ->
            0 < bv_unsigned (snd e)
            /\ bv_unsigned (fst e) mod 4096 = 0
            /\ bv_unsigned (snd e) mod 4096 = 0
            /\ AIMG_TOP <= bv_unsigned (fst e)
            /\ AHI_LO + 4096 <= bv_unsigned (fst e)
            /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 47
            /\ ARESX_LO <= bv_unsigned (fst e))
      /\ (length rx <= 2)%nat
      /\ zsum (map (fun e => bv_unsigned (snd e)) rx) <= 81920
      /\ (forall iv, In iv (vm_maps h) ->
            forall e, In e (vm_reserved h) ->
              bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e)
              \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst iv)).

  Definition akernel (mo : Model) : Prop := akernel_pre mo /\ akernel_resx mo.
  (* The former conjunction as a constant: the result type of [AS_InstMainK.akernel_main]'s
     recorded proof, which builds exactly that conjunction. *)
  Definition akernel_pre_d (mo : Model) : Prop := akernel_pre mo.

  Definition AMODELX : ltac2:(zQ "10!lr4>2mo$0P") := ltac2:(zQ "40!v0!lr4!nn2!ns1\2mo$1@2$0@2$2?1s^1@1$3^1").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Derived.
    Variable mo : ltac2:(zQ "10!lr4$0").
    Hypothesis AKfull : akernel mo.
    (* LPS 727298f3: [AK] keeps naming the former conjunction, so the projections below read
       as before; only the lemmas that need the launch's reserved intervals use [AKfull]. *)
    #[local] Notation AK := (proj1 AKfull) (only parsing).
    Let h := m_vmmaps mo.

    Lemma ak_resx : exists rx : list (word * word),
      vm_reserved h = segments_reserved asegs ++ rx
      /\ (forall e, In e rx ->
            0 < bv_unsigned (snd e)
            /\ bv_unsigned (fst e) mod 4096 = 0
            /\ bv_unsigned (snd e) mod 4096 = 0
            /\ AIMG_TOP <= bv_unsigned (fst e)
            /\ AHI_LO + 4096 <= bv_unsigned (fst e)
            /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 47
            /\ ARESX_LO <= bv_unsigned (fst e))
      /\ (length rx <= 2)%nat
      /\ zsum (map (fun e => bv_unsigned (snd e)) rx) <= 81920
      /\ (forall iv, In iv (vm_maps h) ->
            forall e, In e (vm_reserved h) ->
              bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e)
              \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst iv)).
    Proof. exact (proj2 AKfull). Qed.

    (* LPS 727298f3: a range above the image and below [ARESX_LO] misses the whole ledger: the
       image's reservations end at [AIMG_TOP], the launch's pair starts at [ARESX_LO]. *)
    Lemma ak_resf : forall a k : word, AIMG_TOP <= bv_unsigned a ->
      bv_unsigned a + bv_unsigned k <= ARESX_LO -> region_free (vm_reserved h) a k = true.
    Proof.
      intros a k Ha Hk. destruct ak_resx as [rx [Hr [Hok _]]]. ndestruct AK as (K1 & _).
      rewrite Hr. apply region_free_introZ. intros e sz He.
      apply in_app_or in He as [He|He].
      - specialize (K1 (e, sz) He). cbn [fst snd] in K1. pose proof (bv_unsigned_in_range _ k). right. lia.
      - pose proof (Hok (e, sz) He) as (_ & _ & _ & _ & _ & _ & HK). cbn [fst] in HK. left. lia.
    Qed.
    (* LPS 727298f3: a range inside a mapping misses the whole ledger, by the mappings' apartness
       from it ([akernel_resx]'s last conjunct); no upper bound on the range is needed. *)
    Lemma ak_resf_inside : forall a k : word,
      map_contains (vm_maps h) a k = true -> region_free (vm_reserved h) a k = true.
    Proof.
      intros a k Hmc. destruct ak_resx as [rx [_ [_ [_ [_ HD]]]]].
      unfold map_contains in Hmc. apply existsb_exists in Hmc as [iv [Hiv Hb]].
      cbv beta in Hb. apply andb_true_iff in Hb as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2.
      apply region_free_introZ. intros e sz He.
      specialize (HD iv Hiv (e, sz) He). cbn [fst snd] in HD.
      destruct HD as [HD|HD]; [left | right]; lia.
    Qed.
    (* LPS 727298f3: the allocator's [RESF] premise ([AS_Refill2], [AS_Refill3], [AS_Refill4],
       [AS_Rta], [AS_LcDealloc], [AS_RecyclePrim]) names windows inside the primary region, which
       is mapped, so it is keyed on [map_contains]; the [AHI_LO] premise is kept and unused. *)
    Lemma ak_resf_hi : forall a k : word, AHI_LO <= bv_unsigned a ->
      map_contains (vm_maps h) a k = true -> region_free (vm_reserved h) a k = true.
    Proof. intros a k _ Hmc. exact (ak_resf_inside a k Hmc). Qed.
    (* [comment removed for export] *)
    Lemma ak_hcov : hcnt (vm_maps h) <= AHC0 + zlen (hsec st) /\ hlen (vm_maps h) <= AHL0 + zsum (map sc_map_size (hsec st))
                    /\ (forall sc, In sc (as_sec st) -> 0 <= sc_map_size sc <= ASECMAX).
    Proof. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _). exact K10. Qed.

    (* [comment removed for export] *)
    Lemma ak_atop : alloc_top h = hceil.
    Proof. ndestruct AK as (_ & (_ & K2) & _). exact K2. Qed.
    (* [comment removed for export] *)

    Lemma ak_tmaps : forall x : word, a_thr s <= bv_unsigned x < a_thr s + kPageSize -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. ndestruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_cmaps : forall x : word, a_ctx s <= bv_unsigned x < a_ctx s + 160 -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. ndestruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_sbmaps : forall x : word, a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. ndestruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_pmaps : forall x : word, a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. ndestruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_fsmaps : forall x : word, a_fsb s <= bv_unsigned x < a_fsb s + AFS_SIZE -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. ndestruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_hsm_full : forall x : word, sh AHI_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. ndestruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.

    Lemma ak_prim : forall (a n : word) (c : Z), 0 <= c < kNumClasses -> RB s c <= bv_unsigned a ->
      bv_unsigned a + bv_unsigned n <= RB s c + kRegionSize -> map_contains (vm_maps h) a n = true.
    Proof. ndestruct AK as (_ & _ & _ & K4 & _). exact K4. Qed.
    Lemma ak_pamc : forall a n : word, a_pa s <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= a_pa s + kPtrArrayReserve ->
      map_contains (vm_maps h) a n = true.
    Proof. ndestruct AK as (_ & _ & _ & _ & K4 & _). exact K4. Qed.
    Lemma ak_hsmc : forall a n : word, sh AHI_LO <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh aceil ->
      map_contains (vm_maps h) a n = true.
    Proof. ndestruct AK as (_ & _ & _ & _ & _ & K4 & _). exact K4. Qed.

    Lemma ak_zr_sb : ltac2:(zQ "f0!vb!lv9!iqa!in4!hjc!mgd!v0!j0!mi5!ml6!lv1!kt6!ub!v6!hhe>1x@1$e@1$0#k0>0@2$6@2$c@1$1?1s@2$3@1$0#k0^1@2$d@2$3@1$0#k0^1@2$2@2$2@1$1?1s$9$8@3$7$4@2$b^2@1$a?1s$5").
    Proof. ndestruct AK as (_ & _ & _ & _ & _ & _ & K5 & _). exact K5. Qed.
    Lemma ak_zr_pa : ltac2:(zQ "e0!vb!lsd!in4!hjc!mgd!v0!j0!mj2!lv1!kt6!iqa!ub!v6!hhe>1x@1$d@1$0#k0>0@2$5@2$b@1$1?1s@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@2$a@1$1?1s$7@3$6$3@2$9^2@1$8?1s$4").
    Proof. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & K5 & _). exact K5. Qed.
    Lemma ak_zrsh : ltac2:(zQ "e0!vb!s6!in4!hjc!js0!v0!j0!lv1!rd!sb!kt6!ub!v6!hhe>1x@1$d@1$0#k0>0@2$5@2$b@1$1$8@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@1$1@1$9?5HCEIL@3$6$3@2$a^2@1$7?1s$4").
    Proof. intros x Hx. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & K5 & _). apply (proj1 (K5 x Hx)). Qed.
    Lemma ak_lsh : ltac2:(zQ "e0!vb!s6!in4!hjc!js0!v0!j0!mma!rd!sb!kt6!ub!v6!hhe>1x@1$d@1$0#k0>0@2$5@2$b@1$1$8@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@1$1@1$9?5HCEIL@3$6$3@2$a^2@1$7?1s$4").
    Proof. intros x Hx. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & K5 & _). apply (proj2 (K5 x Hx)). Qed.
    (* [comment removed for export] *)
    Lemma ak_sec_noacc : forall sc (x : word), In sc (as_sec st) -> sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc ->
      in_rangesb x (vm_noaccess h) = false.
    Proof. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K6b & _). exact K6b. Qed.
    (* [comment removed for export] *)
    Lemma ak_secmaps : forall sc, In sc (as_sec st) -> In (wz (sc_map_beg sc), wz (sc_map_size sc)) (vm_maps h).
    Proof. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K7 & _). exact K7. Qed.

    (* [comment removed for export] *)
    Lemma ak_shland : forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true.
    Proof. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8a & _). exact K8a. Qed.
    Lemma ak_lsmc : forall a n : word, sh AIMG_TOP <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO ->
      map_contains (vm_maps h) a n = true.
    Proof. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8b & _). exact K8b. Qed.
    Lemma ak_zrsl : ltac2:(zQ "e0!vb!s6!in4!hjc!js0!v0!j0!lt5!lv1!mg1!kt6!ub!v6!hhe>1x@1$d@1$0#k0>0@2$5@2$b@1$1$7@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@1$1$9@3$6$3@2$a^2@1$8?1s$4").
    Proof. intros x Hx. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8c & _). apply (proj1 (K8c x Hx)). Qed.
    Lemma ak_lsl : ltac2:(zQ "e0!vb!s6!in4!hjc!js0!v0!j0!lt5!mma!mg1!kt6!ub!v6!hhe>1x@1$d@1$0#k0>0@2$5@2$b@1$1$7@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@1$1$9@3$6$3@2$a^2@1$8?1s$4").
    Proof. intros x Hx. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8c & _). apply (proj2 (K8c x Hx)). Qed.
    Lemma ak_imgr : forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved h) = true.
    Proof. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K9 & _). exact K9. Qed.
    Lemma ak_zrsh2 : ltac2:(zQ "h10!vb!s6!in4!v0!ub!v6!hjc!js0!j0!ls8!lt5!lv1!rd!mg1!sb!kt6!hhe>1x@1$h0@1$0#k0>0@2$9@2$3@2$4@1$1$c@2$2@1$0#k0^1@2$5@2$2@1$0#k0^1@1$1@1$e?5HCEIL@2$3@2$4@1$1$a@2$2@1$0#k0^1@2$5@2$2@1$0#k0^1@1$1$d@3$8$6@2$f^2@1$b?1s$7").
    Proof. intros x [Hx|Hx]; [apply ak_zrsh; exact Hx| apply ak_zrsl; exact Hx]. Qed.
    Lemma ak_shmc2 : forall a n : word, 0 < bv_unsigned n ->
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      map_contains (vm_maps h) a n = true.
    Proof. intros a n Hn [[H1 H2]|[H1 H2]]; [apply ak_hsmc| apply ak_lsmc]; assumption. Qed.
    Lemma ak_shrf2 : forall a n : word,
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      region_free (vm_reserved h) a n = true.
    (* LPS 727298f3: [ak_resf] carries the upper premise the launch's pair costs; both bands end
       far below [ARESX_LO] ([sh_ceiling_range]: [sh aceil] is at most 0x10007fef8000). *)
    Proof.
      intros a n [[H1 H2]|[H1 H2]]; pose proof sh_ceiling_range;
        apply ak_resf;
        unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP, ARESX_LO, ALOWSH_LO in *; lia.
    Qed.
    (* [comment removed for export] *)
    Lemma ak_shna : forall a n : word,
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      region_free (vm_noaccess h) a n = true.
    Proof. ndestruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11). exact K11. Qed.

    (* [comment removed for export] *)
  End Derived.

  (* [comment removed for export] *)
  Lemma akernel_mat : ltac2:(zQ "30!lr4!ns1!nsc>2mo$0>3mo'$0>0@1$1^2>0@2$2^3^2@1$1^3").
  Proof. intros mo mo' AK SB. unfold akernel, akernel_resx in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact AK. Qed.
  Lemma AMODELX_mat : ltac2:(zQ "30!lr4!nu6!nsc>2mo$0>3mo'$0>0@1$1^2>0@2$2^3^2@1$1^3").
  Proof. intros mo mo' [A K] SB. split; [eapply AMODEL_mat; eassumption| eapply akernel_mat; eassumption]. Qed.

  (* [comment removed for export] *)
  Lemma awin_vis_wmono : ltac2:(zQ "70!vb!nv1!hhe!jr6!kk9!jq8!oj9>1m$5>2m'>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@1$1^2>0@3$6$4^3^2@1$1^3").
  Proof. intros m m' V W x Hx. apply W. apply V. exact Hx. Qed.
End X.

(* LPS 727298f3: [akernel_resx] of a model whose ledger is the image's reservations followed by the
   launch's vDSO/vvar pair ([AsanPlanSound.co_res]): the pair sits below [vdso_top], the page
   below [min mmap_base alloc_top]; with [mmap_base_min <= mmap_base] and [alloc_top = hceil]
   (far above it) its base is at least 0x154555542001, its top at most [hceil < 2 ^ 47]. *)
Lemma akernel_resx_intro : forall (mo : Model) kb,
  vm_reserved (m_vmmaps mo) = segments_reserved asegs ++ vdso_reserved kb (vdso_top (m_vmmaps mo)) ->
  mmap_base_min <= bv_unsigned (vm_mmap_base (m_vmmaps mo)) ->
  alloc_top (m_vmmaps mo) = hceil ->
  (forall iv, In iv (vm_maps (m_vmmaps mo)) -> forall e, In e (vm_reserved (m_vmmaps mo)) ->
     bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e)
     \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst iv)) ->
  akernel_resx mo.
Proof.
  intros mo kb Hr Hmb AT Hd.
  pose proof aceil_facts as AF.
  pose proof (vdso_text_pages_pos kb) as TP1. pose proof (vdso_text_pages_le kb) as TP2.
  assert (U : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z)
    by (intros z Hz; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; exact Hz).
  assert (TB : 0x154555556001 <= vdso_top (m_vmmaps mo) <= hceil /\ vdso_top (m_vmmaps mo) mod 4096 = 0).
  { unfold vdso_top, mmap_top, page_round_down_Z, page_size. rewrite AT. unfold mmap_base_min in Hmb.
    Z.div_mod_to_equations. lia. }
  set (T := vdso_top (m_vmmaps mo)) in *.
  assert (SH : vdso_reserved kb T =
    [(Z_to_bv 64 (T - vdso_len kb), Z_to_bv 64 (vdso_vvar_pages * page_size));
     (Z_to_bv 64 (T - vdso_len kb + vdso_vvar_pages * page_size), Z_to_bv 64 (vdso_text_pages kb * page_size))]).
  { unfold vdso_reserved. cbv zeta.
    replace (T - vdso_len kb <? page_size) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. unfold vdso_len, vdso_vvar_pages, page_size. lia. }
  unfold akernel_resx. cbv zeta. exists (vdso_reserved kb T).
  split; [exact Hr|].
  split.
  { intros e He. rewrite SH in He. unfold vdso_len, vdso_vvar_pages, page_size in *.
    unfold AIMG_TOP, AHI_LO, ARESX_LO.
    destruct He as [<-|[<-|[]]]; cbn [fst snd]; rewrite !U by lia; Z.div_mod_to_equations; lia. }
  split; [rewrite SH; cbn [length]; lia|].
  split.
  { rewrite SH. cbn [map zsum fst snd].
    rewrite !U by (unfold vdso_len, vdso_vvar_pages, page_size in *; lia).
    unfold vdso_len, vdso_vvar_pages, page_size in *. lia. }
  exact Hd.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot_cov : ltac2:(zQ "20!lr4!oo2>1d$1>2mo$0P") := ltac2:(zQ "h30!vb!in4!v0!oob!op3!iqa!ub!v6!opb!hjc!js0!j0!ls8!lr4!mq3!lrd!oo2!kt6!hhe\1d$h0\2mo$d>1x@1$h2@1$0#k0>0@2$c@2$2@2$6@1$3^3@2$1@1$0#k0^1@2$7@2$1@1$0#k0^1@2$5@1$3^3@2$8+h0+hggg0@2$2@2$6@1$4^3@2$1@1$0#k0^1@2$7@2$1@1$0#k0^1@2$5@1$4^3@2$8+8+ogg0@3$b$9@2$h1^2@1$f@1$e^3$a").
Lemma depot_cov_mat : ltac2:(zQ "40!lr4!oq1!oo2!nsc>1d$2>2mo$0>3mo'$0>0@2$1^3^2>0@2$3^3^2@2$1^5^3").
Proof. intros d mo mo' C SB. unfold depot_cov in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact C. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AGAP : ltac2:(zQ "20!h9!lr4>1n$0>2mo$1P") := ltac2:(zQ "h01!vb!hhe!hk4!rd!iqa!iu9!hp5!h9!lr4!moc!mp6!mq3!lrd!mk7!oqd!ub&@2$2@1$1@1$0#k0@1$1@1$0#k0\1n$7\2mo$8=1h$9@1$b^1=1E@1$6~0@3$5~0@1$d^1@1$c^1@2$f@2$4@2$4$3@3$e^4$3^1^4@1$a^2").
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma cost_high_bound : ltac2:(zQ "d0!vb!iqa!hhe!hp5!hk4!h9!it3!iu2!rd!oqd!ub!v6!opb>1n$5>1E@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0>0@2$bZ^2@2$a@3$9^3$8^2@2$1@1$7^2@2$c@1$6^2@2$1^3+hgg0").
Proof.
  intros n E Hn. induction E as [|e E IH]; [rewrite cost_nil, hlen_nil, hcnt_nil; lia|].
  rewrite cost_cons, hlen_cons, hcnt_cons. unfold ecost, ehigh.
  destruct (Z.ltb_spec AHI_LO (KInv.ehi e)) as [H|H].
  - unfold KInv.ehi, KInv.elo in *. pose proof (bv_unsigned_in_range _ (fst e)). lia.
  - lia.
Qed.
(* LPS 727298f3: the launch's extra reserved intervals lie above the gate [AHI_LO], so they charge
   the ledger: each entry costs its own size plus [n + 4096] ([SecGap.ecost]), so a list of them
   costs at most its total size plus its length times that. *)
Lemma cost_le_sizes : forall n E, 0 < n ->
  cost n AHI_LO E <= zsum (map (fun e => bv_unsigned (snd e)) E) + Z.of_nat (length E) * (n + 4096).
Proof.
  intros n E Hn. induction E as [|e E IH]; [rewrite cost_nil; cbn; lia|].
  rewrite cost_cons. cbn [map length zsum]. unfold ecost.
  pose proof (bv_unsigned_in_range 64 (snd e)). unfold KInv.ehi, KInv.elo.
  rewrite Nat2Z.inj_succ.
  destruct (AHI_LO <? bv_unsigned (fst e) + bv_unsigned (snd e)); lia.
Qed.
(* LPS 727298f3: the room grows by what the launch's pair costs the ledger: at most two entries
   ([akernel_resx]'s count) of at most 81920 bytes together (its size bound), each charging
   [n + 4096]. *)
Theorem AGAP_of_akernel : forall s mo n, akernel s mo -> 0 < n ->
  AHI_LO + (AHL0 + zsum (map sc_map_size (hsec (a_st s)))) + (AHC0 + zlen (hsec (a_st s))) * (n + 4096) + n
    + (81920 + 2 * (n + 4096)) <= hceil ->
  AGAP n mo.
Proof.
  intros s mo n AK Hn ROOM. unfold AGAP.
  npose AK as ((K1 & (_ & K2) & _) & RX). npose (ak_hcov s mo AK) as (C1 & C2 & _).
  rewrite K2, cost_app.
  destruct RX as [rx [Hrx [Hok [Hcnt Hsz]]]].
  (* the image's reservations cost nothing: they end at or below AIMG_TOP, below the gate *)
  assert (R0seg : cost n AHI_LO (segments_reserved asegs) = 0).
  { assert (L : Forall (fun e => KInv.ehi e <= AHI_LO) (segments_reserved asegs)).
    { apply Forall_forall. intros e He. specialize (K1 e He). unfold KInv.ehi, AHI_LO, AIMG_TOP in *. lia. }
    clear - L Hn. induction L as [|e E He L IH]; [apply cost_nil|]. rewrite cost_cons, IH, (ecost_below n AHI_LO e He). reflexivity. }
  assert (R0 : cost n AHI_LO (vm_reserved (m_vmmaps mo)) <= 81920 + 2 * (n + 4096)).
  { rewrite Hrx, cost_app, R0seg. pose proof (cost_le_sizes n rx Hn) as CLS.
    assert (ML : Z.of_nat (length rx) * (n + 4096) <= 2 * (n + 4096))
      by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  pose proof (cost_high_bound n (vm_maps (m_vmmaps mo)) Hn) as CB.
  pose proof (hcnt_nonneg (vm_maps (m_vmmaps mo))). pose proof (hlen_nonneg (vm_maps (m_vmmaps mo))).
  assert (M : hcnt (vm_maps (m_vmmaps mo)) * (n + 4096) <= (AHC0 + zlen (hsec (a_st s))) * (n + 4096)) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

End HCW.

(* [comment removed for export] *)
Ltac acb ::=
  let K := fresh "ACEILB" in
  pose proof (conj aceil_facts sh_ceiling_range
              : (0x7fff7f800000 <= aceil <= 0x7fffff800000 /\ aceil mod 4096 = 0 /\ aceil <= hceil < aceil + 4096)
                /\ (0x10006fef8000 <= sh aceil <= 0x10007fef8000)) as K.
(* [comment removed for export] *)
